#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
hwpdoc.py — 한글(HWPX) 문서 자동 작성 엔진 v1.0

쓰던 한글 양식의 디자인(글꼴·문단 모양·표 테두리·제목 상자·머리말·로고·쪽 설정)은 그대로 두고
내용만 새로 채운 .hwpx 파일을 만든다. Claude(스킬)와 ChatGPT(맞춤 GPT)의 코드 실행 환경에서
똑같이 동작하도록 파일 하나로 만들었다. 필요한 것: Python 3.9 이상, lxml(두 환경 모두 기본 설치).

명령줄
  python hwpdoc.py analyze 양식.hwpx [-o 개요.txt]        양식 분석 + 지금 내용을 '개요'로 꺼내기
  python hwpdoc.py build   양식.hwpx 개요.txt -o 결과.hwpx  개요대로 같은 디자인의 새 문서 만들기
  python hwpdoc.py slots   양식.hwpx                        칸 목록 보기(신청서·서식 칸 채우기용)
  python hwpdoc.py fill    양식.hwpx 값.json -o 결과.hwpx    칸만 채우기(나머지는 100% 그대로)
  python hwpdoc.py check   결과.hwpx                        결과 점검(파일 구조·공문 표기·개인정보)
  python hwpdoc.py text    파일.hwpx|파일.hwp                글자만 꺼내기(.hwp는 읽기만 가능)

파이썬에서
  import sys; sys.path.insert(0, '<이 파일이 있는 폴더>'); import hwpdoc
  print(hwpdoc.analyze('양식.hwpx', '개요.txt'))
  print(hwpdoc.build('양식.hwpx', '개요.txt', '결과.hwpx'))
"""
from __future__ import annotations

import argparse
import collections
import copy
import difflib
import io
import json
import math
import os
import random
import re
import shutil
import statistics
import struct
import subprocess
import sys
import unicodedata
import zipfile
import zlib

try:
    from lxml import etree
except ImportError:  # pragma: no cover
    raise SystemExit('lxml 패키지가 필요합니다 (pip install lxml)')

VERSION = '1.0'

NS_HP = 'http://www.hancom.co.kr/hwpml/2011/paragraph'
NS_HH = 'http://www.hancom.co.kr/hwpml/2011/head'
NS_HC = 'http://www.hancom.co.kr/hwpml/2011/core'
NS_OPF = 'http://www.idpf.org/2007/opf/'
NS_HA = 'http://www.hancom.co.kr/hwpml/2011/app'

PARSER = etree.XMLParser(remove_blank_text=False, huge_tree=True,
                         resolve_entities=False, no_network=True)


def P(tag):
    return '{%s}%s' % (NS_HP, tag)


def H(tag):
    return '{%s}%s' % (NS_HH, tag)


def C(tag):
    return '{%s}%s' % (NS_HC, tag)


def local(tag):
    if not isinstance(tag, str):
        return ''
    return tag.rsplit('}', 1)[-1]


class HwpError(Exception):
    """사용자에게 그대로 보여 줄 오류."""


HWP_BINARY_MSG = (
    '이 파일은 예전 형식(.hwp)이라 디자인을 그대로 옮길 수 없습니다. '
    '한글에서 이 파일을 열고 [파일] → [다른 이름으로 저장하기] → 아래쪽 "파일 형식"을 '
    '"HWPX 문서(*.hwpx)"로 바꿔 저장한 뒤, 그 .hwpx 파일을 올려 주세요. '
    '(내용을 참고만 할 때는 .hwp도 글자를 읽을 수 있습니다.)'
)
LOCKED_MSG = (
    '%s: 한글 파일 이름인데 내용이 잠겨 있어 읽을 수 없습니다. 기관 문서보안(DRM)이 걸린 파일로 보입니다. '
    '문서보안 프로그램에서 보안을 해제한(일반 문서로 바꾼) 파일로 다시 올려 주세요. '
    '해제 방법은 기관 전산(정보화) 담당자에게 물어보세요.'
)


def not_hwp_msg(path, data):
    """zip(HWPX)도 옛 한글(HWP)도 아닌 파일 안내. 이름이 한글 파일이면 문서보안(DRM)으로 잠긴 것일 때가 많다."""
    name = os.path.basename(path)
    if not data:
        return '%s: 빈 파일입니다. 원본 파일을 다시 올려 주세요.' % name
    if data[:5] == b'%PDF-':
        return '%s: PDF 파일입니다. 양식은 한글 파일(.hwpx)로 올려 주세요.' % name
    if name.lower().endswith(('.hwpx', '.hwp')):
        return LOCKED_MSG % name
    return '%s: 한글 HWPX 파일이 아닙니다.' % name

# ---------------------------------------------------------------- 패키지(zip)


class Package:
    """HWPX(zip) 묶음. 바꾼 항목만 갈아 끼우고 나머지는 원본 그대로 다시 묶는다."""

    def __init__(self, path):
        self.path = path
        if not os.path.isfile(path):
            raise HwpError('파일을 찾지 못했습니다: %s' % path)
        with open(path, 'rb') as f:
            data = f.read()
        if data[:8] == b'\xd0\xcf\x11\xe0\xa1\xb1\x1a\xe1':
            raise HwpError(HWP_BINARY_MSG)
        if data[:2] != b'PK':
            raise HwpError(not_hwp_msg(path, data))
        try:
            self.zf = zipfile.ZipFile(io.BytesIO(data))
        except zipfile.BadZipFile:
            raise HwpError('%s: 파일이 손상되어 열 수 없습니다.' % os.path.basename(path))
        self.names = [i.filename for i in self.zf.infolist()]
        self.data = {n: self.zf.read(n) for n in self.names}
        self.changed = {}
        self.removed = set()

    def xml(self, name):
        return etree.fromstring(self.changed.get(name, self.data[name]), PARSER)

    def _decl(self, name):
        b = self.data.get(name, b'')
        if b.startswith(b'<?xml'):
            return b[:b.find(b'?>') + 2]
        return b'<?xml version="1.0" encoding="UTF-8" standalone="yes" ?>'

    def put_xml(self, name, root):
        self.changed[name] = self._decl(name) + etree.tostring(root, encoding='UTF-8')

    def section_names(self):
        try:
            hpf = self.xml('Contents/content.hpf')
            items = {it.get('id'): it.get('href') for it in hpf.iter('{%s}item' % NS_OPF)}
            secs = []
            for ref in hpf.iter('{%s}itemref' % NS_OPF):
                href = items.get(ref.get('idref'))
                if href and re.search(r'section\d+\.xml$', href) and href in self.data:
                    secs.append(href)
            if secs:
                return secs
        except Exception:
            pass
        found = [n for n in self.names if re.match(r'Contents/section\d+\.xml$', n)]
        return sorted(found, key=lambda s: int(re.findall(r'\d+', s)[-1]))

    def drop_section(self, name):
        self.removed.add(name)
        try:
            hpf = self.xml('Contents/content.hpf')
            for it in list(hpf.iter('{%s}item' % NS_OPF)):
                if it.get('href') == name:
                    sid = it.get('id')
                    it.getparent().remove(it)
                    for ref in list(hpf.iter('{%s}itemref' % NS_OPF)):
                        if ref.get('idref') == sid:
                            ref.getparent().remove(ref)
            self.put_xml('Contents/content.hpf', hpf)
        except Exception:
            pass

    def save(self, out):
        d = os.path.dirname(os.path.abspath(out))
        os.makedirs(d, exist_ok=True)
        order = [n for n in self.names if n == 'mimetype'] + [n for n in self.names if n != 'mimetype']
        with zipfile.ZipFile(out, 'w') as z:
            for n in order:
                if n in self.removed:
                    continue
                info = self.zf.getinfo(n)
                zi = zipfile.ZipInfo(n, date_time=info.date_time)
                stored = n == 'mimetype' or info.compress_type == zipfile.ZIP_STORED
                zi.compress_type = zipfile.ZIP_STORED if stored else zipfile.ZIP_DEFLATED
                zi.external_attr = info.external_attr
                z.writestr(zi, self.changed.get(n, self.data[n]))
            for n, b in self.changed.items():
                if n not in self.names and n not in self.removed:
                    z.writestr(zipfile.ZipInfo(n), b, compress_type=zipfile.ZIP_DEFLATED)


class Header:
    """header.xml 에서 글자 크기·굵기·글꼴 이름을 읽는다(읽기 전용)."""

    def __init__(self, root):
        self.root = root
        self.char = {c.get('id'): c for c in root.iter(H('charPr'))}
        self.para = {p.get('id'): p for p in root.iter(H('paraPr'))}
        self.fonts = {}
        for ff in root.iter(H('fontface')):
            if ff.get('lang') == 'HANGUL':
                for f in ff.findall(H('font')):
                    self.fonts[f.get('id')] = f.get('face')

    def pt(self, cid):
        c = self.char.get(cid)
        try:
            return int(c.get('height')) / 100.0
        except Exception:
            return 10.0

    def bold(self, cid):
        c = self.char.get(cid)
        return c is not None and c.find(H('bold')) is not None

    def face(self, cid):
        c = self.char.get(cid)
        fr = c.find(H('fontRef')) if c is not None else None
        return self.fonts.get(fr.get('hangul'), '') if fr is not None else ''


# ---------------------------------------------------------------- 글자 다루기

T_SPECIAL = {P('tab'): '\t', P('lineBreak'): '\n'}
T_SPACE = {P('nbSpace'): ' ', P('fwSpace'): ' ', P('hyphen'): '-'}
OBJ_LOCAL = {'tbl', 'pic', 'container', 'rect', 'ellipse', 'arc', 'polygon', 'curve', 'line',
             'connectLine', 'textart', 'ole', 'equation', 'chart', 'video', 'compose', 'dutmal',
             'btn', 'radioBtn', 'checkBtn', 'comboBox', 'edit', 'listBox', 'scrollBar'}
SETUP_CTRL = {'header', 'footer', 'pageNum', 'pageNumCtrl', 'newNum', 'pageHiding', 'autoNum'}


def t_text(t):
    s = t.text or ''
    for ch in t:
        s += T_SPECIAL.get(ch.tag, '') or T_SPACE.get(ch.tag, '')
        s += ch.tail or ''
    return s


def para_runs(p):
    return [c for c in p if c.tag == P('run')]


def run_ts(r):
    return [c for c in r if c.tag == P('t')]


def run_has_control(r):
    return any(c.tag != P('t') for c in r)


def para_text(p):
    return ''.join(t_text(t) for r in para_runs(p) for t in run_ts(r))


def set_t(t, s):
    """hp:t 내용을 s로 바꾼다. 탭·줄바꿈은 원래 있던 요소를 다시 쓰고, 모자라면 새로 만든다."""
    pool = collections.defaultdict(list)
    for ch in list(t):
        key = T_SPECIAL.get(ch.tag)
        if key:
            ch.tail = None
            pool[key].append(ch)
        t.remove(ch)
    t.text = None
    last = None
    buf = []

    def flush():
        txt = ''.join(buf)
        buf.clear()
        if not txt:
            return
        if last is None:
            t.text = (t.text or '') + txt
        else:
            last.tail = (last.tail or '') + txt

    for c in s:
        if c in ('\t', '\n'):
            flush()
            if pool[c]:
                el = pool[c].pop(0)
                t.append(el)
            elif c == '\t':
                el = etree.SubElement(t, P('tab'))
                el.set('width', '4000')
                el.set('leader', '0')
                el.set('type', '1')
            else:
                el = etree.SubElement(t, P('lineBreak'))
            last = el
        else:
            buf.append(c)
    flush()


def strip_lineseg(e):
    for ls in list(e.iter(P('linesegarray'))):
        ls.getparent().remove(ls)


def remove_ctrls(p, keep_objects=True):
    """복제한 문단에서 머리말·쪽번호·필드 같은 조판 부호를 뺀다(원본 디자인 요소는 틀에 남아 있다)."""
    for r in para_runs(p):
        for c in list(r):
            ln = local(c.tag)
            if ln in ('secPr', 'ctrl'):
                r.remove(c)
            elif not keep_objects and ln != 't':
                r.remove(c)


def t_segments(p):
    segs = []
    pos = 0
    for r in para_runs(p):
        for t in run_ts(r):
            s = t_text(t)
            segs.append([r, t, pos, pos + len(s)])
            pos += len(s)
    return segs, pos


def _anchor(segs, idx):
    for sg in segs:
        if sg[2] <= idx < sg[3]:
            return sg
    return None


def ensure_t(p, charpr=None):
    for r in para_runs(p):
        if not run_has_control(r) or run_ts(r):
            if not run_ts(r):
                etree.SubElement(r, P('t'))
            return
    runs = para_runs(p)
    if runs:
        etree.SubElement(runs[-1], P('t'))
        return
    r = etree.SubElement(p, P('run'))
    r.set('charPrIDRef', charpr or '0')
    etree.SubElement(r, P('t'))
    ls = p.find(P('linesegarray'))
    if ls is not None:
        p.remove(r)
        ls.addprevious(r)


def fill_para(p, a, b, new_prefix, new_label, new_body, body_charpr=None, body_seg=None):
    """견본 문단 p의 [0,a)=머리기호, [a,b)=항목명, [b,끝)=본문 자리에 새 글자를 넣는다.
    글자를 담는 run(글자 모양)은 견본의 것을 그대로 쓴다."""
    segs, n = t_segments(p)
    if not segs:
        ensure_t(p, body_charpr)
        segs, n = t_segments(p)
        a = b = 0
    pa = _anchor(segs, 0) if a > 0 else None
    la = _anchor(segs, a) if b > a else None
    ba = body_seg or (_anchor(segs, b) if b < n else None)
    if ba is None:
        ba = la or pa or segs[-1]
    texts = {id(sg[1]): '' for sg in segs}
    texts[id((pa or la or ba)[1])] += new_prefix
    texts[id((la or ba)[1])] += new_label
    texts[id(ba[1])] += new_body
    for sg in segs:
        set_t(sg[1], texts[id(sg[1])])
    body_run = ba[0]
    if (body_charpr and not run_has_control(body_run)
            and (pa is None or pa[0] is not body_run) and (la is None or la[0] is not body_run)):
        body_run.set('charPrIDRef', body_charpr)
    # 글자가 비게 된 run 정리(조판 요소가 있는 run은 남긴다)
    runs = para_runs(p)
    for r in runs:
        if len(para_runs(p)) <= 1:
            break
        if run_has_control(r):
            continue
        if all(not t_text(t) for t in run_ts(r)):
            p.remove(r)
    strip_lineseg(p)


# ---------------------------------------------------------------- 머리 기호(□ ○ - ※ 1. 가. …)

MARK_RE = re.compile(
    r'^(\s*)('
    r'[□■◆◇▣▢❏❑◼◻]'
    r'|[○◦ㅇ◉◎]'
    r'|[●•▪]'
    r'|[∙·ㆍ▫]'
    r'|[-–—―ㅡ]'
    r'|[※*]'
    r'|[▶▷►➢➤→⇒]'
    r'|[①-⑳➀-➉❶-❿➊-➓]'
    r'|[ⅠⅡⅢⅣⅤⅥⅦⅧⅨⅩ]{1,3}\.?'
    r'|(?:I|II|III|IV|V|VI|VII|VIII|IX|X)\.'
    r'|\d{1,2}\.(?!\d)'
    r'|\d{1,2}\)'
    r'|\(\d{1,2}\)'
    r'|[가나다라마바사아자차카타파하]\.'
    r'|[가나다라마바사아자차카타파하]\)'
    r'|\([가나다라마바사아자차카타파하]\)'
    r'|<\d{1,2}>'
    r')(\s*)'
)
NUMBERED = {'roman', 'num.', 'num)', '(num)', 'ga.', 'ga)', '(ga)', 'circnum', '<num>'}


def marker_class(g):
    if not g:
        return 'plain'
    if g in '□■◆◇▣▢❏❑◼◻':
        return 'box'
    if g in '○◦ㅇ◉◎':
        return 'circle'
    if g in '●•▪':
        return 'dot'
    if g in '∙·ㆍ▫':
        return 'middot'
    if g in '-–—―ㅡ':
        return 'dash'
    if g in '※*':
        return 'note'
    if g in '▶▷►➢➤→⇒':
        return 'arrow'
    if re.fullmatch('[①-⑳➀-➉❶-❿➊-➓]', g):
        return 'circnum'
    if re.fullmatch(r'[ⅠⅡⅢⅣⅤⅥⅦⅧⅨⅩ]{1,3}\.?|[IVX]+\.', g):
        return 'roman'
    if re.fullmatch(r'\d{1,2}\.', g):
        return 'num.'
    if re.fullmatch(r'\d{1,2}\)', g):
        return 'num)'
    if re.fullmatch(r'\(\d{1,2}\)', g):
        return '(num)'
    if re.fullmatch(r'[가-하]\.', g):
        return 'ga.'
    if re.fullmatch(r'[가-하]\)', g):
        return 'ga)'
    if re.fullmatch(r'\([가-하]\)', g):
        return '(ga)'
    if re.fullmatch(r'<\d{1,2}>', g):
        return '<num>'
    return 'plain'


CLASS_NAME = {
    'box': '□', 'circle': '○', 'dot': '●', 'middot': '·', 'dash': '-', 'note': '※', 'arrow': '▶',
    'circnum': '①', 'roman': 'Ⅰ.', 'num.': '1.', 'num)': '1)', '(num)': '(1)', 'ga.': '가.',
    'ga)': '가)', '(ga)': '(가)', '<num>': '<1>', 'plain': '(기호 없는 본문)',
    'shape': '[소제목]', 'plainhead': '[제목줄]',
}

FALLBACK = {
    'box': ['shape', 'plainhead', 'num.', 'roman', 'circle', 'tablehead'],
    'shape': ['tablehead', 'box', 'plainhead', 'roman', 'num.', 'circle'],
    'tablehead': ['shape', 'box', 'plainhead', 'roman', 'num.', 'circle'],
    'plainhead': ['shape', 'box', 'roman', 'num.', 'circle'],
    'roman': ['tablehead', 'shape', 'box', 'plainhead', 'num.'],
    'num.': ['box', 'shape', 'tablehead', 'roman', 'circle', '(num)'],
    '<num>': ['num.', 'box', 'shape'],
    'circle': ['dot', 'middot', 'dash', 'plain'],
    'dot': ['circle', 'middot', 'dash', 'plain'],
    'middot': ['dash', 'dot', 'circle', 'plain'],
    'dash': ['middot', 'dot', 'circle', 'plain', 'note'],
    'note': ['dash', 'middot', 'circle', 'plain'],
    'arrow': ['dash', 'middot', 'circle', 'plain', 'note'],
    'circnum': ['(num)', 'num)', 'circle', 'dash'],
    '(num)': ['num)', 'circnum', 'circle', 'dash'],
    'num)': ['(num)', 'circnum', 'circle', 'dash'],
    'ga.': ['ga)', '(ga)', 'num)', 'circle', 'dash'],
    'ga)': ['ga.', '(ga)', 'num)', 'dash'],
    '(ga)': ['ga)', 'ga.', 'dash'],
    'plain': ['circle', 'dash', 'middot', 'dot', 'note'],
}


def split_marker(text):
    m = MARK_RE.match(text)
    if not m:
        lead = re.match(r'\s*', text).group(0)
        return lead, '', '', text[len(lead):]
    return m.group(1), m.group(2), m.group(3), text[m.end():]


LABEL_RE = re.compile(r'^([^\s:：][^:：\n]{0,15}?)(\s*[:：]\s*)(?=\S)')


def split_label(rest):
    m = LABEL_RE.match(rest)
    if not m:
        return None
    label, sep = m.group(1), m.group(2)
    if not re.search('[가-힣A-Za-z]', label) or len(label.strip()) > 12:
        return None
    after = rest[m.end():m.end() + 1]
    if label[-1:].isdigit() and after.isdigit():
        return None
    return label, sep, rest[m.end():]


def disp_len(s):
    return sum(1.0 if ord(c) > 0x2000 else 0.55 for c in s)


ROMAN_U = 'ⅠⅡⅢⅣⅤⅥⅦⅧⅨⅩ'
ROMAN_A = ['I', 'II', 'III', 'IV', 'V', 'VI', 'VII', 'VIII', 'IX', 'X']
CIRC = '①②③④⑤⑥⑦⑧⑨⑩⑪⑫⑬⑭⑮⑯⑰⑱⑲⑳'
CIRC_FAMILIES = [CIRC, '➀➁➂➃➄➅➆➇➈➉', '❶❷❸❹❺❻❼❽❾❿', '➊➋➌➍➎➏➐➑➒➓']
GANADA = '가나다라마바사아자차카타파하'


def number_format(s):
    s = s.strip()
    if re.fullmatch(r'\d+', s):
        return ('arabic', len(s) if s.startswith('0') else 0)
    if len(s) == 1 and s in ROMAN_U:
        return ('roman_u', 0)
    if s in ROMAN_A:
        return ('roman_a', 0)
    for fam in CIRC_FAMILIES:
        if len(s) == 1 and s in fam:
            return ('circ', CIRC_FAMILIES.index(fam))
    return None


def format_number(fmt, k):
    kind, width = fmt
    if kind == 'arabic':
        return str(k).zfill(width) if width else str(k)
    if kind == 'roman_u':
        return ROMAN_U[(k - 1) % 10]
    if kind == 'roman_a':
        return ROMAN_A[(k - 1) % 10]
    if kind == 'circ':
        fam = CIRC_FAMILIES[width]
        return fam[(k - 1) % len(fam)]
    return str(k)


def auto_number(cls, k, example=''):
    """번호 종류(cls)의 k번째 기호. example(양식의 기호)의 모양을 따른다."""
    if cls == 'roman':
        g = ROMAN_U[(k - 1) % 10]
        if example and example.strip()[:1] in 'IVX':
            g = ROMAN_A[(k - 1) % 10]
        return g + ('.' if (not example or example.strip().endswith('.')) else '')
    if cls == 'circnum':
        fmt = number_format(example.strip()) if example else None
        return format_number(fmt if fmt and fmt[0] == 'circ' else ('circ', 0), k)
    return {'num.': '%d.' % k, 'num)': '%d)' % k, '(num)': '(%d)' % k, '<num>': '<%d>' % k,
            'ga.': GANADA[(k - 1) % 14] + '.', 'ga)': GANADA[(k - 1) % 14] + ')',
            '(ga)': '(%s)' % GANADA[(k - 1) % 14]}.get(cls, example or '')


# ---------------------------------------------------------------- 표

def has_inline_obj(p):
    """문단 바로 아래 글 조각에 표·그림·도형이 있는가(제목 상자·표 문단)."""
    return any(local(c.tag) in OBJ_LOCAL for r in para_runs(p) for c in r)


def attach_ctrls(p, ctrls):
    """머리말·쪽 번호 같은 설정(ctrls: [(글자 모양 번호, ctrl)])을 문단 p 맨 앞에 단다."""
    runs = para_runs(p)
    for cp, ctrl in ctrls:
        r = etree.SubElement(p, P('run'))
        r.set('charPrIDRef', cp or (runs[0].get('charPrIDRef') if runs else '0'))
        r.append(copy.deepcopy(ctrl))
        if runs:
            p.remove(r)
            runs[0].addprevious(r)


def first_table(p):
    for r in para_runs(p):
        for c in r:
            if c.tag == P('tbl'):
                return c
    return None


def tc_text(tc):
    sub = tc.find(P('subList'))
    if sub is None:
        return ''
    return '\n'.join(para_text(x) for x in sub.findall(P('p'))).strip('\n')


def table_grid(tbl):
    rows = []
    for tr in tbl.findall(P('tr')):
        rows.append([tc_text(tc) for tc in tr.findall(P('tc'))])
    return rows


def tc_span(tc):
    sp = tc.find(P('cellSpan'))
    if sp is None:
        return 1, 1
    return int(sp.get('colSpan', '1') or 1), int(sp.get('rowSpan', '1') or 1)


def tc_size(tc):
    sz = tc.find(P('cellSz'))
    if sz is None:
        return 0, 0
    return int(sz.get('width', '0') or 0), int(sz.get('height', '0') or 0)


TITLE_WORD_RE = re.compile(r'계획|보고|결과|안내|공고|신청|운영|개최|추진|방안|지침|선발|모집|사업|평가|협조|요청|알림|제출|현황|실적|매뉴얼|가이드|설명|교육|행사|프로그램|제안')
ORG_RE = re.compile(r'[(\[<]?\s*[가-힣A-Za-z·\s]{0,20}(대학교|대학|학교|본부|센터|과|팀|처|원|청|부|실|단|위원회|협동조합|재단|공사|공단)\s*[)\]>]?')
DATE_LINE_RE = re.compile(r'[\d\s.,년월일()~\-–·]+(월|일|\.)?\s*(\([월화수목금토일]\))?')

ORG_RE = re.compile(r'(?:국립|사단법인|재단법인|\(사\)|\(재\)|㈜|\(주\)|주식회사)?\s*[가-힣A-Za-z]{2,}'
                    r'(?:대학교|대학|고등학교|중학교|초등학교|학교|협동조합|재단|진흥원|연구원|공사|공단|도청|시청|군청|구청|'
                    r'교육지원청|교육청|위원회|센터|본부|협회|사업단|사무소|주식회사)(?![가-힣])')
META_TABLE_RE = re.compile(r'결\s*재|담\s*당|과\s*장|팀\s*장|처\s*장|부\s*장|국\s*장|원\s*장|총\s*장|기\s*안|검\s*토|협\s*조|작성자|보고일|전\s*결')

# 목차 줄: "Ⅰ. 추진 배경 ⇥ 3"처럼 끝에 탭(또는 점선) + 쪽 번호
TOC_TAIL_RE = re.compile(r'(\t[\s.·…‥_\-]*|\s*[.·…‥]{3,}\s*)(\d{1,3})\s*$')
TOC_HEAD_RE = re.compile(r'^(목차|차례|contents|tableofcontents)$', re.I)
TOC_FALLBACK = {'attach': ['roman', 'num.', 'plain'], 'roman': ['num.', 'plain'],
                'num.': ['roman', 'd.d', 'plain'], 'd.d': ['num.', 'd.d.d', 'plain'],
                'd.d.d': ['d.d', 'num.', 'plain'], 'plain': ['d.d', 'num.', 'roman']}


def toc_sig(entry):
    """목차 줄의 단계 표시(Ⅰ. / 1. / 1.1 / 1.1.1 / 붙임 …)."""
    lead, g, trail, rest = split_marker(entry.strip())
    if g.strip():
        return marker_class(g.strip())
    if re.match(r'\d+\.\d+\.\d+', rest):
        return 'd.d.d'
    if re.match(r'\d+\.\d+', rest):
        return 'd.d'
    if re.match(r'(붙임|부록|별첨|참고)', rest):
        return 'attach'
    return 'plain'


def split_toc(text):
    """목차 줄 → (제목, 쪽 번호)."""
    s = text.rstrip()
    m = TOC_TAIL_RE.search(s)
    if not m:
        return s.strip(), ''
    return s[:m.start()].strip(), m.group(2)


def lead_number(rest):
    """'II 추진 경과'·'2 추진 경과'처럼 앞에 붙은 번호 → (번호, 나머지 글). 없으면 (0, rest)."""
    m = re.match(r'^\s*([ⅠⅡⅢⅣⅤⅥⅦⅧⅨⅩ]|(?:VIII|VII|VI|IV|IX|III|II|I|V|X)(?=[\s.)])|\d{1,2}|[①-⑳➀-➉❶-❿➊-➓])[.)]?\s+(?=\S)', rest)
    if not m:
        return 0, rest
    tok = m.group(1)
    k = int(tok) if tok.isdigit() else _number_of(tok)
    return (k, rest[m.end():]) if k else (0, rest)


# ---------------------------------------------------------------- 양식 분석

class Block:
    def __init__(self, i, el):
        self.i = i
        self.el = el
        self.kind = 'blank'
        self.text = ''
        self.flags = set()
        self.key = None
        self.cls = 'plain'
        self.glyph = ''
        self.lead = ''
        self.trail = ''
        self.label = None
        self.a = 0
        self.b = 0
        self.body_cp = None
        self.body_pt = 0.0
        self.body_bold = False
        self.tno = None
        self.target = el
        self.numcell = None
        self.textcell = 0
        self.numtext = ''
        self.tsig = None


class Role:
    def __init__(self, key, cls, glyph, labeled):
        self.key = key
        self.cls = cls
        self.glyph = glyph
        self.labeled = labeled
        self.blocks = []
        self.ex = None
        self.body_cp = None
        self.lead = ''
        self.trail = ''
        self.sep = ''
        self.a = 0
        self.b = 0
        self.pt = 0.0
        self.bold = False
        self.numfmt = None
        self.numcls = None
        self.numdot = False
        self.numcell = None
        self.textcell = 0
        self.first = 0
        self.rank = 1

    def display(self):
        if self.cls in ('shape', 'tablehead'):
            base = '[소제목]' if self.rank <= 1 else '[소제목%d]' % self.rank
        elif self.cls == 'plainhead':
            base = '[제목줄]'
        elif self.cls == 'plain':
            base = '(기호 없는 본문)'
        elif self.cls in NUMBERED:
            base = CLASS_NAME[self.cls]
        else:
            base = self.glyph or CLASS_NAME.get(self.cls, self.cls)
        if self.labeled:
            base += ' 항목 : 내용'
        return base


def frame_marks(els, pkg=None):
    """els(틀 블록·머리말 등)와 바탕쪽에 든 그림 수와 기관 이름 목록."""
    pics = 0
    texts = []
    roots = list(els)
    if pkg is not None:
        for n in pkg.names:
            if re.match(r'Contents/masterpage\d*\.xml$', n):
                try:
                    roots.append(pkg.xml(n))
                except Exception:
                    pass
    for el in roots:
        pics += sum(1 for _ in el.iter(P('pic')))
        texts += [para_text(p) for p in el.iter(P('p'))]
    orgs = []
    for s in texts:
        for m in ORG_RE.finditer(s):
            name = m.group(0).strip()
            if name not in orgs:
                orgs.append(name)
    return pics, orgs


class RefDoc:
    """양식(참고 문서)을 읽고 틀·문단 종류(견본)·간격 규칙·표 견본을 정리한다."""

    def __init__(self, path):
        self.pkg = Package(path)
        self.header = Header(self.pkg.xml('Contents/header.xml'))
        self.sections = self.pkg.section_names()
        if not self.sections:
            raise HwpError('문서 본문(section)을 찾지 못했습니다.')
        self.sec_name = self.sections[0]
        self.root = self.pkg.xml(self.sec_name)
        self.blocks = [Block(i, el) for i, el in enumerate(c for c in self.root if c.tag == P('p'))]
        self.warnings = []
        self.photo_n = 0  # build에서 붙인 사진 자리 번호
        self.hedit = HeaderEditor(self.pkg)
        self._classify()
        self._find_title_and_frame()
        self._roles()
        self._spacing()
        self._tables()

    # -- 블록 종류
    def _classify(self):
        tno = 0
        for b in self.blocks:
            p = b.el
            flags = set()
            small_obj = True
            for r in para_runs(p):
                for c in r:
                    ln = local(c.tag)
                    if ln == 't':
                        continue
                    if ln == 'secPr':
                        flags.add('secPr')
                    elif ln == 'ctrl':
                        flags.add('ctrl')
                        for cc in c:
                            if local(cc.tag) in SETUP_CTRL:
                                flags.add('setupctrl')
                    elif ln == 'tbl':
                        flags.add('tbl')
                    elif ln in OBJ_LOCAL:
                        flags.add('obj')
                        sz = c.find(P('sz'))
                        try:
                            if int(sz.get('width')) > 6000 or int(sz.get('height')) > 6000:
                                small_obj = False
                        except Exception:
                            pass
            b.flags = flags
            b.text = para_text(p)
            st = b.text.strip()
            b.target = p
            if 'tbl' in flags:
                tno += 1
                b.tno = tno
                b.kind = 'table'
                head = None if st else self._head_cells(first_table(p))
                if head:
                    # 한 줄짜리 짧은 제목 표 = 표로 만든 장 제목(「Ⅰ. 추진 배경」 상자, 「Ⅰ | 추진 배경」 칸)
                    b.kind = 'tablehead'
                    b.numcell, b.textcell, b.numtext, b.target = head
                    b.text = para_text(b.target)
            elif 'obj' in flags:
                b.kind = 'shapehead' if (st and small_obj and len(st) <= 60) else 'object'
            elif st:
                b.kind = 'text'
            elif flags & {'secPr', 'ctrl'}:
                b.kind = 'setup'
            else:
                b.kind = 'blank'
            if b.kind in ('text', 'shapehead', 'tablehead'):
                self._measure(b)
        self._find_toc()

    @staticmethod
    def _head_cells(tbl):
        """한 줄짜리 제목 표면 (번호 칸, 글 칸, 번호 글자, 글 문단)을, 아니면 None을 돌려준다."""
        trs = tbl.findall(P('tr'))
        if len(trs) != 1:
            return None
        cells = trs[0].findall(P('tc'))
        if not 1 <= len(cells) <= 4:
            return None
        num = txt = None
        numtext = ''
        for i, tc in enumerate(cells):
            s = tc_text(tc).strip()
            if not s:
                continue
            paras = [x for x in _tc_paras(tc) if para_text(x).strip()]
            if len(paras) != 1 or len(s) > 40 or re.search('[→⇒➜]', s):
                return None
            if len(cells) > 1 and num is None and txt is None and number_format(s.rstrip('.')):
                num, numtext = i, s
                continue
            if txt is not None:
                return None
            txt = (i, paras[0])
        if txt is None:
            return None
        return num, txt[0], numtext, txt[1]

    def _find_toc(self):
        """목차(끝에 탭·점선 + 쪽 번호인 줄이 3줄 이상 이어짐)를 찾아 견본에서 뺀다."""
        cand = set(b.i for b in self.blocks if b.kind == 'text' and len(b.text.strip()) <= 90
                   and TOC_TAIL_RE.search(b.text.rstrip()))
        runs, cur = [], []
        for b in self.blocks:
            if b.kind in ('blank', 'setup'):
                continue
            if b.i in cand:
                cur.append(b)
                continue
            if len(cur) >= 3:
                runs.append(cur)
            cur = []
        if len(cur) >= 3:
            runs.append(cur)
        self.toc_samples = collections.OrderedDict()
        self.toc_head = None
        for run in runs:
            for b in run:
                b.kind = 'toc'
                b.tsig = toc_sig(split_toc(b.text)[0])
                if b.tsig not in self.toc_samples or 'ctrl' in self.blocks[self.toc_samples[b.tsig]].flags:
                    self.toc_samples[b.tsig] = b.i
            j = run[0].i - 1
            while j >= 0 and self.blocks[j].kind in ('blank', 'setup'):
                j -= 1
            if j >= 0 and self.blocks[j].kind in ('text', 'tablehead') \
                    and TOC_HEAD_RE.match(re.sub(r'\s', '', self.blocks[j].text)):
                self.blocks[j].kind = 'tochead'
                if self.toc_head is None:
                    self.toc_head = j

    def _measure(self, b):
        """머리 기호·항목명 위치와 본문 글자 모양(가장 많이 쓴 것)을 잰다."""
        hdr = self.header
        lead, g, trail, rest = split_marker(b.text)
        b.lead, b.glyph, b.trail = lead, g, trail
        b.a = len(lead) + len(g) + len(trail)
        lab = split_label(rest)
        if lab and b.kind == 'text':
            b.label = lab
            b.b = b.a + len(lab[0]) + len(lab[1])
        else:
            b.b = b.a
        cnt = collections.Counter()
        segs, n = t_segments(b.target)
        for r, t, s, e in segs:
            lo = max(s, b.b)
            if e > lo:
                cnt[r.get('charPrIDRef')] += len(re.sub(r'\s', '', t_text(t)[lo - s:]))
        if not cnt:
            for r, t, s, e in segs:
                cnt[r.get('charPrIDRef')] += len(t_text(t).strip())
        if cnt:
            b.body_cp = cnt.most_common(1)[0][0]
            b.body_pt = hdr.pt(b.body_cp)
            b.body_bold = hdr.bold(b.body_cp)

    def _is_data_table(self, b):
        if b.kind != 'table':
            return False
        rows = table_grid(first_table(b.el))
        full = [r for r in rows if sum(1 for c in r if c.strip()) >= 2]
        if len(full) < 2:
            return False
        return not META_TABLE_RE.search(' '.join(sum(rows, [])))

    def _max_pt(self, p):
        mx = 0.0
        for r in para_runs(p):
            if any(t_text(t).strip() for t in run_ts(r)):
                mx = max(mx, self.header.pt(r.get('charPrIDRef')))
        return mx

    def _title_in(self, region):
        """region 블록들(표 칸 포함)에서 제목을 찾는다: 큰 글자 + 제목다운 낱말, 기관명·날짜는 뺀다."""
        best = None
        for b in region:
            ps = list(b.el.iter(P('p')))
            for k, p in enumerate(ps):
                txt = para_text(p).strip()
                if not txt or len(txt) > 80:
                    continue
                mx = self._max_pt(p)
                score = mx
                if TITLE_WORD_RE.search(txt):
                    score += 3
                if ORG_RE.fullmatch(txt) or DATE_LINE_RE.fullmatch(txt):
                    score -= 6
                if p.getparent() is not self.root:
                    score += 0.5
                if best is None or score > best[0] + 0.01:
                    best = (score, b.i, k, mx)
        if not best:
            return None
        _, bi, k, mx = best
        ps = list(self.blocks[bi].el.iter(P('p')))
        parent = ps[k].getparent()
        group = [k]
        if parent is not self.root:
            # 같은 칸에서 붙어 있는 비슷한 크기의 줄은 한 제목(앞뒤 모두)
            def same(j):
                if not (0 <= j < len(ps)) or ps[j].getparent() is not parent:
                    return False
                t = para_text(ps[j]).strip()
                return bool(t) and abs(self._max_pt(ps[j]) - mx) <= 3.1 and not DATE_LINE_RE.fullmatch(t)
            j = k - 1
            while same(j):
                group.insert(0, j)
                j -= 1
            j = k + 1
            while same(j):
                group.append(j)
                j += 1
        nxt = []
        if parent is self.root:
            # 본문 문단 제목: 바로 다음 블록이 같은 크기 글자면 두 줄 제목
            nb = bi + 1
            while nb < len(self.blocks) and self.blocks[nb].kind == 'text' and len(nxt) < 2:
                q = self.blocks[nb].el
                if abs(self._max_pt(q) - mx) > 0.6 or self.blocks[nb].glyph:
                    break
                nxt.append(nb)
                nb += 1
        texts = [para_text(ps[g]).strip() for g in group] + [para_text(self.blocks[j].el).strip() for j in nxt]
        return {'block': bi, 'ps': group, 'next': nxt, 'text': '\n'.join(texts), 'pt': mx}

    # -- 제목과 틀(그대로 두는 앞부분)
    def _find_title_and_frame(self):
        blocks = self.blocks
        self.cover = False
        cover_end = None
        for b in blocks[1:45]:
            if b.el.get('pageBreak') == '1':
                cover_end = b.i
                break
        if cover_end:
            pre = blocks[:cover_end]
            bodyish = any(b.kind == 'text' and b.glyph and len(b.text.strip()) > 25 for b in pre)
            bodyish = bodyish or any(self._is_data_table(b) for b in pre)
            ntext = sum(1 for b in pre if b.kind in ('text', 'shapehead', 'tablehead'))
            if not bodyish and ntext <= 12:
                self.cover = True
        if self.cover:
            self.title = self._title_in(blocks[:cover_end])
            self.frame_end = cover_end
        else:
            first_struct = len(blocks)
            for b in blocks:
                if b.kind == 'shapehead' or (b.kind == 'text' and b.glyph) or self._is_data_table(b):
                    first_struct = b.i
                    break
                if b.kind == 'tablehead' and b.glyph:
                    first_struct = b.i
                    break
            self.title = self._title_in(blocks[:min(first_struct, 12)])
            tb = self.title['block'] + len(self.title['next']) if self.title else -1
            i = 0
            while i < len(blocks):
                b = blocks[i]
                if i <= tb or b.kind in ('setup', 'blank'):
                    i += 1
                    continue
                if (b.kind == 'text' and not b.glyph and len(b.text.strip()) <= 60 and i <= tb + 4
                        and re.search(r'\d{4}\s*[.년]|\d{1,2}\s*[.월]\s*\d{1,2}|[가-힣]+(과|팀|처|센터|부서|실|단|본부|위원회)(\s|$|\))|작성|담당|보고|^[-–(<\[]', b.text.strip())):
                    i += 1
                    continue
                if b.kind == 'table' and META_TABLE_RE.search(' '.join(sum(table_grid(first_table(b.el)), []))):
                    i += 1
                    continue
                break
            self.frame_end = i
        self.body_new_page = (self.frame_end < len(blocks) and self.frame_end > 0
                              and blocks[self.frame_end].el.get('pageBreak') == '1')
        # 틀 뒤쪽(본문 중간)에 들어 있는 머리말·쪽 번호 같은 설정
        self.moved_ctrls = []
        for b in blocks[self.frame_end:]:
            if 'setupctrl' in b.flags:
                for r in para_runs(b.el):
                    for c in r:
                        if local(c.tag) == 'ctrl' and any(local(cc.tag) in SETUP_CTRL for cc in c):
                            self.moved_ctrls.append((r.get('charPrIDRef'), c))
        # 틀(표지 등) 안의 글자 — @바꾸기 안내용
        self.frame_texts = []
        tset = set()
        if self.title:
            # 제목은 @제목으로 바꾸므로 뺀다(줄바꿈이 든 한 문단 제목도, 줄마다 나뉜 제목도)
            tset = set(self.title['text'].split('\n')) | {self.title['text'].strip()}
        for b in blocks[:self.frame_end]:
            for p in b.el.iter(P('p')):
                s = para_text(p).strip()
                if s and s not in tset and s not in self.frame_texts:
                    self.frame_texts.append(s)
        # 새 문서에 그대로 남는 그림(로고일 수 있음)·기관 이름 — 다른 기관 양식인지 확인하라고 알린다
        self.frame_pics, self.frame_orgs = frame_marks([b.el for b in blocks[:self.frame_end]]
                                                       + [c for _, c in self.moved_ctrls], self.pkg)

    # -- 문단 종류(견본)
    def _roles(self):
        hdr = self.header
        body = [b for b in self.blocks[self.frame_end:] if b.kind in ('text', 'shapehead', 'tablehead')]
        pts = []
        for b in body:
            if b.kind == 'text' and b.body_pt:
                pts += [b.body_pt] * max(1, len(b.text.strip()))
        pts.sort()
        self.median_pt = pts[len(pts) // 2] if pts else 0.0
        glyphs = collections.defaultdict(collections.Counter)
        for b in body:
            if b.kind == 'shapehead':
                b.cls = 'shape'
            elif b.kind == 'tablehead':
                b.cls = 'tablehead'
            elif b.glyph:
                b.cls = marker_class(b.glyph.strip())
                glyphs[b.cls][b.glyph.strip()] += 1
            else:
                big = b.body_pt >= self.median_pt + 1.5
                boldhead = b.body_bold and b.body_pt >= self.median_pt and len(b.text.strip()) <= 40
                b.cls = 'plainhead' if (self.median_pt and (big or boldhead)) else 'plain'
        self.roles = collections.OrderedDict()
        thead_keys = {}
        for b in body:
            g = b.glyph.strip()
            key = b.cls
            if b.cls == 'tablehead':
                # 모양이 다른 제목 표(장 제목 칸·절 제목 상자)는 따로 센다
                tbl = first_table(b.el)
                sig = (len(tbl.findall('.//' + P('tc'))), b.numcell, b.textcell, round(hdr.pt(b.body_cp)))
                if sig not in thead_keys:
                    thead_keys[sig] = 'tablehead' + ('' if not thead_keys else str(len(thead_keys) + 1))
                key = thead_keys[sig]
            elif (b.cls not in NUMBERED and b.cls not in ('plain', 'plainhead', 'shape')
                    and len(glyphs[b.cls]) > 1):
                key += ':' + g
            if b.label:
                key += '+label'
            b.key = key
            if key not in self.roles:
                self.roles[key] = Role(key, b.cls, g, bool(b.label))
            self.roles[key].blocks.append(b.i)
        for role in self.roles.values():
            occ = [self.blocks[i] for i in role.blocks]
            cp = collections.Counter()
            for b in occ:
                segs, n = t_segments(b.target)
                for r, t, s, e in segs:
                    lo = max(s, b.b)
                    if e > lo:
                        cp[r.get('charPrIDRef')] += len(re.sub(r'\s', '', t_text(t)[lo - s:]))
            role.body_cp = cp.most_common(1)[0][0] if cp else occ[0].body_cp
            pp = collections.Counter(b.target.get('paraPrIDRef') for b in occ)
            top_pp = pp.most_common(1)[0][0]

            def score(b):
                s = 0
                if b.target.get('paraPrIDRef') == top_pp:
                    s += 4
                if b.body_cp == role.body_cp:
                    s += 2
                if not (b.flags & {'secPr', 'ctrl'}):
                    s += 8
                return s
            ex = max(occ, key=lambda b: (score(b), -b.i))
            role.ex = ex.i
            role.lead, role.trail = ex.lead, ex.trail
            role.a, role.b = ex.a, ex.b
            role.sep = ex.label[1] if ex.label else ''
            role.pt = hdr.pt(role.body_cp)
            role.bold = hdr.bold(role.body_cp)
            role.first = min(role.blocks)
            if role.cls == 'tablehead':
                role.numcell, role.textcell = ex.numcell, ex.textcell
                if ex.numcell is not None:
                    role.numfmt = number_format(ex.numtext.rstrip('.'))
                    role.numdot = ex.numtext.endswith('.')
                elif role.glyph:
                    role.numcls = marker_class(role.glyph)
            if role.cls == 'shape':
                nested = []
                for r in para_runs(ex.el):
                    for c in r:
                        if local(c.tag) in OBJ_LOCAL:
                            nested += [t for t in c.iter(P('t')) if t_text(t).strip()]
                if len(nested) == 1:
                    fmt = number_format(t_text(nested[0]))
                    if fmt:
                        role.numfmt = fmt
        # 제목 계열은 본문에 먼저 나오는 것이 윗단계
        heads = sorted([r for r in self.roles.values() if r.cls in HEAD_CLASSES and not r.labeled],
                       key=lambda r: r.first)
        self.heading_order = [r.cls for r in heads]
        self.heading_keys = [r.key for r in heads]
        # 상자형 제목([소제목], [소제목2] …)도 먼저 나오는 것이 윗단계
        self.box_roles = [r for r in heads if r.cls in ('shape', 'tablehead')]
        for k, r in enumerate(self.box_roles):
            r.rank = k + 1

    # -- 빈 줄 간격 규칙
    def _spacing(self):
        self.blank_ex = None
        cnt = collections.Counter()
        for b in self.blocks[self.frame_end:]:
            if b.kind == 'blank':
                cnt[(b.el.get('paraPrIDRef'), tuple(r.get('charPrIDRef') for r in para_runs(b.el)))] += 1
        sig_to_block = {}
        for b in self.blocks:
            if b.kind == 'blank':
                sig = (b.el.get('paraPrIDRef'), tuple(r.get('charPrIDRef') for r in para_runs(b.el)))
                sig_to_block.setdefault(sig, b.i)
        if cnt:
            self.blank_ex = sig_to_block[cnt.most_common(1)[0][0]]
        elif sig_to_block:
            self.blank_ex = list(sig_to_block.values())[0]
        self.pair_space = collections.defaultdict(collections.Counter)
        self.role_space = collections.defaultdict(collections.Counter)
        self.space_examples = {}
        seq = []
        prev = None
        for b in self.blocks[self.frame_end:]:
            if b.kind == 'blank':
                seq.append(b.i)
                continue
            if b.kind == 'setup':
                continue
            key = self.block_key(b)
            sig = tuple((self.blocks[j].el.get('paraPrIDRef'),
                         tuple(r.get('charPrIDRef') for r in para_runs(self.blocks[j].el))) for j in seq)
            self.space_examples.setdefault(sig, tuple(seq))
            if prev is not None:
                self.pair_space[(prev, key)][sig] += 1
                self.role_space[key][sig] += 1
            seq = []
            prev = key

    def block_key(self, b):
        if b.kind == 'toc':
            return 'toc:' + (b.tsig or 'plain')
        if b.kind == 'tochead':
            return 'tochead'
        if b.kind == 'tablehead':
            return b.key or 'tablehead'
        if b.kind == 'table':
            return 'table%d' % b.tno
        if b.kind == 'object':
            return 'object%d' % b.i
        return b.key or 'plain'

    def spacing(self, prev, key):
        c = self.pair_space.get((prev, key))
        if not c:
            c = self.role_space.get(key)
        if not c and key.startswith('table'):
            merged = collections.Counter()
            for k, v in self.role_space.items():
                if k.startswith('table'):
                    merged.update(v)
            c = merged
        if not c:
            return ()
        sig = c.most_common(1)[0][0]
        return self.space_examples.get(sig, ())

    # -- 표 견본
    def _tables(self):
        self.tables = {}
        for b in self.blocks:
            if b.kind != 'table':
                continue
            tbl = first_table(b.el)
            grid = table_grid(tbl)
            spans = any(tc_span(tc) != (1, 1) for tc in tbl.iter(P('tc')))
            self.tables[b.tno] = {
                'photo': [[photo_cell(tc) for tc in tr.findall(P('tc'))] for tr in tbl.findall(P('tr'))],
                'block': b.i, 'rows': int(tbl.get('rowCnt', len(grid)) or len(grid)),
                'cols': int(tbl.get('colCnt', 0) or 0), 'grid': grid, 'spans': spans,
                'frame': b.i < self.frame_end,
            }
        for t in self.tables.values():
            g = t['grid']
            cells = [c for r in g for c in r]
            t['filled'] = sum(1 for c in cells if c.strip()) / max(1, len(cells))
            t['header'] = bool(g) and len(g) >= 2 and len(g[0]) >= 2 and all(
                c.strip() and len(c.strip()) <= 14 for c in g[0])
            # 사진 표: 사진 칸(큰 그림만 든 칸이나 [사진] 자리)이 든 줄이 3분의 1 이상인 표. 서식형 판정에서 뺀다
            prow = [any(f) or any(PHOTO_RE.match(c) for c in r) for r, f in zip(g, t['photo'] + [[]] * len(g))]
            t['photo_table'] = any(prow) and sum(prow) * 3 >= len(prow)
        self.default_table = self.pick_table(None)

    def pick_table(self, rows):
        """[표] 번호 없이 쓴 표의 견본: 머리 줄이 있는 표, 칸 수가 같은 표, 병합 없는 표를 고른다."""
        body = [k for k, t in self.tables.items() if not t['frame'] and t['filled'] >= 0.5]
        pool = body or [k for k, t in self.tables.items() if not t['frame']] or list(self.tables)
        if not pool:
            return None
        C = max((len(r) for r in rows), default=0) if rows else 0

        def score(k):
            t = self.tables[k]
            s = 4.0 if t['header'] else 0.0
            if C:
                s += 3.0 if t['cols'] == C else -0.5 * abs(t['cols'] - C)
            s += 1.0 if not t['spans'] else 0.0
            s += 0.1 * min(t['rows'], 10) + (1.0 if t['rows'] >= 2 else 0.0)
            return (s, -t['block'])
        return max(pool, key=score)

    # -- 개요 만들기(지금 내용을 개요 문법으로)
    def outline(self):
        out = []
        out.append('// 이 개요를 고쳐서 build 하면 같은 디자인의 새 문서가 됩니다. (// 로 시작하는 줄은 무시)')
        out.append('// 줄 머리: ' + ''.join(r.display() + ' / ' for r in self.roles.values())
                   + ('[표] … [/표] / ' if self.tables else '')
                   + ('[목차] … [/목차] / ' if self.toc_samples else '') + '[쪽나눔] / [빈줄] / [원본 번호]')
        out.append('// 빈 줄 간격은 원본처럼 자동으로 들어갑니다. 개요 안의 빈 줄은 무시됩니다.')
        out.append('// 이 개요를 복사해 바뀐 줄만 고치세요. 안 고친 줄은 원본 모양 그대로, 고친 줄은 그 자리 원본 줄 모양으로 만들어집니다.')
        if self.title:
            out.append('@제목: ' + self.title['text'].replace('\n', '\\n'))
        for s in self.frame_texts[:8]:
            s1 = ' '.join(s.split())   # 줄바꿈이 든 글자도 한 줄로(주석이 끊겨 본문으로 새지 않게, @바꾸기는 띄어쓰기를 가리지 않음)
            out.append('// 표지·머리 글자: "%s" → 바꾸려면 @바꾸기: %s => 새 글자' % (s1, s1))
        first = True
        in_toc = False
        for b in self.blocks[self.frame_end:]:
            if b.kind in ('blank', 'setup'):
                continue
            if b.el.get('pageBreak') == '1' and not (first and self.body_new_page):
                out.append('[쪽나눔]')
            first = False
            if b.kind in ('toc', 'tochead'):
                if not in_toc:
                    out.append('[목차]  // 목차 줄은 "제목 | 쪽 번호". 쪽 번호를 비워 두면("제목 |") 다 만든 뒤 엔진이 채웁니다.')
                    in_toc = True
                if b.kind == 'toc':
                    entry, page = split_toc(b.text)
                    out.append(entry.replace('\t', ' ') + ' | ' + page)
                continue
            if in_toc:
                out.append('[/목차]')
                in_toc = False
            if b.kind == 'table':
                t = self.tables[b.tno]
                out.append('[표 %d]' % b.tno)
                for row, ph in zip(t['grid'], t['photo']):
                    row = ['[사진]' if f else c for c, f in zip(row, ph + [False] * len(row))]
                    s = ' | '.join(c.replace('|', '\\|').replace('\n', '\\n') for c in row)
                    # 첫 칸이나 끝 칸이 비면 양쪽에 | 를 붙여야 빈칸이 빠지지 않는다(사진 칸 줄은 「|  |」)
                    out.append('| %s |' % s if row and not (row[0].strip() and row[-1].strip()) else s)
                out.append('[/표]')
            elif b.kind == 'object':
                out.append('[원본 %d]  // 그림·도형 그대로' % b.i)
            else:
                txt = b.text.strip().replace('\n', '\\n').replace('\t', ' ')
                role = self.roles.get(b.key)
                box = '[소제목]' if not role or role.rank <= 1 else '[소제목%d]' % role.rank
                if b.cls == 'shape':
                    out.append(box + ' ' + b.text[b.a:].strip().replace('\n', '\\n'))
                elif b.cls == 'tablehead':
                    out.append(box + ' ' + txt)
                elif b.cls == 'plainhead':
                    out.append('[제목줄] ' + txt)
                else:
                    out.append(txt)
        if in_toc:
            out.append('[/목차]')
        return '\n'.join(out) + '\n'

    def summary(self):
        hdr = self.header
        L = []
        L.append('[양식 분석] %s' % os.path.basename(self.pkg.path))
        L.append('- 구역 %d개 · 블록 %d개 · 표 %d개' % (len(self.sections), len(self.blocks), len(self.tables)))
        try:
            n, _, saved = gauge_pages(self.pkg)
            line = '- 분량: %d쪽(한글이 저장한 쪽 나눔)' % saved if saved else '- 분량: 약 %d쪽(어림)' % n
            cv = cover_pages(self.pkg, self.frame_end) if self.cover else 0
            if 0 < cv < (saved or n):
                line += ' = 표지 %d쪽 + 본문 %d쪽. 분량 보기·@쪽수는 표지를 뺀 본문 쪽 수로 쓴다' % (cv, (saved or n) - cv)
            L.append(line)
        except Exception:
            pass
        if self.title:
            L.append('- 제목: "%s" (%.0fpt)' % (self.title['text'][:60], self.title['pt']))
        else:
            L.append('- 제목: 찾지 못함')
        if self.cover:
            L.append('- 표지: 있음(블록 0~%d, 그대로 두고 @제목·@바꾸기로 글자만 바꿈)' % (self.frame_end - 1))
        else:
            L.append('- 틀(그대로 두는 앞부분): 블록 0~%d' % (self.frame_end - 1) if self.frame_end else '- 틀: 없음')
        if self.frame_texts:
            L.append('- 틀 안 글자(@바꾸기 대상): ' + ' / '.join('"%s"' % ' '.join(s.split())[:24] for s in self.frame_texts[:8]))
        if self.frame_pics or self.frame_orgs:
            bits = []
            if self.frame_pics:
                bits.append('그림 %d개(로고일 수 있음)' % self.frame_pics)
            if self.frame_orgs:
                bits.append('기관 이름 ' + ', '.join('"%s"' % s for s in self.frame_orgs[:6]))
            L.append('- 확인(새 문서 틀에 그대로 남음): %s → 내 기관 양식이면 그대로 두고, '
                     '다른 기관에서 받은 양식이면 이름은 @바꾸기로 고치고 그림은 한글에서 바꾸거나 지우세요.'
                     % ' · '.join(bits))
        L.append('- 문단 종류(견본):')
        for r in self.roles.values():
            ex = self.blocks[r.ex]
            sample = ex.text.strip().replace('\n', ' ')
            if len(sample) > 38:
                sample = sample[:38] + '…'
            face = hdr.face(r.body_cp)
            L.append('   %-14s %2d회  %s %.0fpt%s%s  예) "%s"' % (
                r.display(), len(r.blocks), face, r.pt, ' 굵게' if r.bold else '',
                ' (표 상자)' if r.cls == 'tablehead' else ' (도형+글자)' if r.cls == 'shape' else '', sample))
        for k, t in self.tables.items():
            head = ' | '.join(c.replace('\n', ' ') for c in (t['grid'][0] if t['grid'] else []))
            if len(head) > 50:
                head = head[:50] + '…'
            note = ' (틀 안)' if t['frame'] else ''
            if k == self.default_table:
                note += ' ← [표] 기본 견본'
            if t['spans']:
                note += ' · 병합 칸 있음'
            L.append('   표 %d: %d행×%d열  첫 줄: %s%s' % (k, t['rows'], t['cols'], head, note))
        if self.toc_samples:
            ntoc = sum(1 for b in self.blocks if b.kind == 'toc')
            L.append('- 목차: %d줄(단계 %d종) → [목차] … [/목차]로 새로 씁니다. 쪽 번호는 자동으로 맞춰지지 않으니 '
                     '한글에서 확인해 고쳐야 합니다.' % (ntoc, len(self.toc_samples)))
        present = {r.cls for r in self.roles.values()}
        missing = [CLASS_NAME[c] for c in ('box', 'circle', 'dash', 'note', 'num.', 'ga.') if c not in present]
        if missing:
            L.append('- 이 양식에 없는 줄 머리: %s → 쓰면 가장 비슷한 견본으로 대신 만듭니다' % ', '.join(missing))
        big = max((t for t in self.tables.values() if not t['photo_table']), key=lambda t: t['rows'] * max(1, t['cols']), default=None)
        ntext = sum(1 for b in self.blocks if b.kind == 'text')
        if big and big['rows'] >= 5 and not data_table(big) and (big['frame'] or ntext <= 6 or big['filled'] < 0.7):
            L.append('- 서식형 문서입니다(큰 표 칸에 적는 신청서·일지·청구서). 새로 짜기(build)보다 '
                     '칸 채우기(slots → fill)가 알맞습니다.')
        if len(self.sections) > 1:
            L.append('- 주의: 구역이 %d개입니다. 새 문서는 첫 구역만 다시 만들고 나머지 구역은 뺍니다.' % len(self.sections))
        pi = scan_personal(self.all_text())
        if pi:
            L.append('- 주의: 양식 안에 개인정보로 보이는 글자가 있습니다(%s). 새 문서에 남지 않게 개요에서 지우세요.' % ', '.join(pi))
        return '\n'.join(L)

    def all_text(self):
        return '\n'.join(para_text(p) for p in self.root.iter(P('p')))


# ---------------------------------------------------------------- 개요 읽기

def split_cells(line):
    s = line.strip()
    if s.startswith('|'):
        s = s[1:]
    if s.endswith('|') and not s.endswith('\\|'):
        s = s[:-1]
    cells = re.split(r'(?<!\\)\|', s)
    return [c.strip().replace('\\|', '|').replace('\\n', '\n') for c in cells]


def clean_md(s):
    s = s.replace('**', '').replace('__', '')
    return s


def parse_outline(text):
    d = {'title': None, 'replace': [], 'frame': None, 'pages': None}
    items = []
    lines = text.splitlines()
    i = 0
    while i < len(lines):
        raw = lines[i].rstrip('\r')
        s = raw.strip()
        i += 1
        if not s or s.startswith('//'):
            continue
        if s.startswith('@'):
            m = re.match(r'@\s*([^:：\s]+)\s*[:：]?\s*(.*)$', s)
            if not m:
                continue
            key, val = m.group(1), m.group(2).strip()
            if key in ('제목', 'title'):
                d['title'] = clean_md(val)
            elif key in ('바꾸기', 'replace'):
                mm = re.split(r'\s*(?:=>|→|➜|->)\s*', val, maxsplit=1)
                if len(mm) == 2:
                    d['replace'].append((mm[0], mm[1]))
            elif key in ('틀', 'frame'):
                nums = [int(x) for x in re.findall(r'\d+', val)]
                if nums:
                    d['frame'] = max(nums) + 1
            elif key in ('쪽수', '쪽', '분량', 'pages'):
                nums = [int(x) for x in re.findall(r'\d+', val)][:2]
                if nums and 0 < min(nums):
                    d['pages'] = (min(nums), max(nums))
            continue
        m = re.match(r'^\[\s*표\s*(\d*)\s*\]$', s)
        if m:
            rows = []
            while i < len(lines):
                r = lines[i].strip()
                i += 1
                if re.match(r'^\[\s*/\s*표\s*\]$', r):
                    break
                if not r or r.startswith('//') or re.fullmatch(r'\|?\s*:?-{2,}:?\s*(\|\s*:?-{2,}:?\s*)*\|?', r):
                    continue
                rows.append([clean_md(c) for c in split_cells(r)])
            items.append(('table', int(m.group(1)) if m.group(1) else None, rows))
            continue
        if re.match(r'^\[\s*(쪽\s*나눔|페이지\s*나눔|새\s*쪽)\s*\]$', s):
            items.append(('pagebreak',))
            continue
        if re.match(r'^\[\s*(목\s*차|차\s*례)\s*\]', s):
            close = re.compile(r'^\[\s*/\s*(목\s*차|차\s*례)\s*\]$')
            entries = []
            if any(close.match(x.strip()) for x in lines[i:]):
                while i < len(lines):
                    r = lines[i].strip()
                    i += 1
                    if close.match(r):
                        break
                    if not r or r.startswith('//'):
                        continue
                    if re.match(r'^\[\s*(쪽\s*나눔|페이지\s*나눔|새\s*쪽)\s*\]$', r):
                        entries.append(('pagebreak',))
                        continue
                    cells = split_cells(r) if re.search(r'(?<!\\)\|', r) else list(split_toc(r))
                    entries.append((clean_md(cells[0]).strip(), (cells[1] if len(cells) > 1 else '').strip()))
            items.append(('toc', entries))
            continue
        if re.match(r'^\[\s*빈\s*줄\s*\]$', s):
            items.append(('blank',))
            continue
        m = re.match(r'^\[\s*원본\s*(\d+)\s*\]', s)
        if m:
            items.append(('orig', int(m.group(1))))
            continue
        m = re.match(r'^\[\s*(소제목|제목줄)\s*(\d?)\s*\]\s*(.*)$', s)
        if m:
            items.append(('text', m.group(1), clean_md(m.group(3)).replace('\\n', '\n'), int(m.group(2) or 1)))
            continue
        m = re.match(r'^(#{1,6})\s', s)
        if m:
            # 마크다운 제목(#, ##)은 가장 얕은 것을 [소제목], 그다음을 [소제목2]로 본다
            top = min(len(re.match(r'#+', x.strip()).group(0)) for x in lines
                      if re.match(r'^#{1,6}\s', x.strip()))
            items.append(('text', '소제목', clean_md(s.lstrip('#').strip()), len(m.group(1)) - top + 1))
            continue
        items.append(('text', None, clean_md(s).replace('\\n', '\n'), 1))
    return d, items


# ---------------------------------------------------------------- 새 문서 조립

class IdState:
    def __init__(self, root):
        self.used = set()
        self.z = 0
        for e in root.iter():
            for a in ('id', 'instid'):
                v = e.get(a)
                if v and v.isdigit():
                    self.used.add(int(v))
            zo = e.get('zOrder')
            if zo and zo.lstrip('-').isdigit():
                self.z = max(self.z, int(zo))

    def new(self):
        while True:
            v = random.randint(1000000000, 2100000000)
            if v not in self.used:
                self.used.add(v)
                return str(v)

    def renew(self, el):
        # 같은 원본 문단·표를 두 번 쓰면 필드(계산식 등) 번호가 겹치므로 시작·끝 짝을 함께 새로 매긴다
        fids = {}
        for e in el.iter(P('fieldBegin')):
            v = e.get('id')
            if v:
                fids[v] = self.new()
                e.set('id', fids[v])
        for e in el.iter(P('fieldEnd')):
            if e.get('beginIDRef') in fids:
                e.set('beginIDRef', fids[e.get('beginIDRef')])
        for e in el.iter():
            ln = local(e.tag)
            if ln in OBJ_LOCAL:
                v = e.get('id')
                if v and v != '0':
                    e.set('id', self.new())
                if e.get('instid'):
                    e.set('instid', self.new())
                par = e.getparent()
                if par is not None and par.tag == P('run') and e.get('zOrder') is not None:
                    self.z += 1
                    e.set('zOrder', str(self.z))


HEAD_CLASSES = {'box', 'shape', 'plainhead', 'roman', 'num.', '<num>', 'tablehead'}


def resolve_role(doc, tag, glyph, labeled, rest='', level=1):
    roles = doc.roles
    if not roles:
        return None
    if tag == '소제목' and doc.box_roles:
        if level <= len(doc.box_roles):
            return doc.box_roles[level - 1], True
        return doc.box_roles[-1], False

    def pick(cls, exact=None):
        cands = [r for r in roles.values() if r.cls == cls]
        if not cands:
            return None
        if exact:
            ex = [r for r in cands if r.glyph == exact]
            if ex:
                cands = ex
            else:
                top = collections.Counter()
                for r in cands:
                    top[r.glyph] += len(r.blocks)
                g = top.most_common(1)[0][0]
                cands = [r for r in cands if r.glyph == g]
        lab = [r for r in cands if r.labeled == labeled]
        cands = lab or cands
        return max(cands, key=lambda r: len(r.blocks))

    if tag == '소제목':
        order = list(doc.heading_order) + ['shape', 'tablehead', 'plainhead', 'box', 'roman', 'num.', 'circle']
        want = order[0]
    elif tag == '제목줄':
        order = ['plainhead'] + list(doc.heading_order) + ['shape', 'box', 'roman', 'num.']
        want = 'plainhead'
    else:
        want = marker_class(glyph)
        order = [want] + FALLBACK.get(want, [])
        if want in HEAD_CLASSES and (labeled or disp_len(rest) > 30):
            # '1. 홍보 : 누리집 게시'처럼 항목·문장형 줄은 제목 상자보다 ○ 항목 견본이 어울린다
            order = [want] + [c for c in ('circle', 'dot', 'dash', 'middot', 'plain') if c != want] + order[1:]
    for k, cls in enumerate(order):
        r = pick(cls, glyph if (k == 0 and glyph) else None)
        if r:
            return r, (cls == want)
    r = max(roles.values(), key=lambda r: len(r.blocks))
    return r, False


LEVEL = {'roman': 0, 'tablehead': 0, 'box': 1, 'shape': 1, 'plainhead': 1, 'num.': 1, '<num>': 1,
         'circle': 2, 'dot': 2, 'num)': 2, 'circnum': 2, 'ga.': 2, 'plain': 2,
         'dash': 3, 'middot': 3, 'arrow': 3, '(num)': 3, 'ga)': 3, '(ga)': 3, 'note': 3}
BULLET = {'box', 'circle', 'dot', 'middot', 'dash', 'arrow', 'note'}


def _number_of(glyph):
    """기호의 번호(①→1, Ⅲ.→3, ➁→2). 모르면 0."""
    g = glyph.strip().rstrip('.')
    for fam in CIRC_FAMILIES:
        if len(g) == 1 and g in fam:
            return fam.index(g) + 1
    if len(g) == 1 and g in ROMAN_U:
        return ROMAN_U.index(g) + 1
    if g in ROMAN_A:
        return ROMAN_A.index(g) + 1
    return 0


def make_prefix(role, tag, glyph, counters):
    """새 줄의 머리 부분(앞 공백 + 기호 + 뒤 공백). 양식의 기호 모양을 우선한다."""
    want = 'shape' if tag == '소제목' else 'plainhead' if tag == '제목줄' else marker_class(glyph)
    gcls = marker_class(glyph) if glyph else None

    def next_no(cls, example):
        counters[role.key] = counters.get(role.key, 0) + 1
        return auto_number(cls, counters[role.key], example)
    if role.cls == 'tablehead':
        if role.numcell is not None:
            return ''  # 번호는 번호 칸에 따로 넣는다(make_text_block)
        if glyph and gcls in NUMBERED:
            return role.lead + glyph + (role.trail or ' ')
        if role.numcls in NUMBERED:
            return role.lead + next_no(role.numcls, role.glyph) + (role.trail or ' ')
        return role.lead + (role.glyph + role.trail if role.glyph else '')
    if role.cls in ('shape', 'plainhead'):
        if glyph and gcls in NUMBERED:
            return role.lead + glyph + ' '
        return role.lead
    deeper = '  ' * max(0, LEVEL.get(want, 2) - LEVEL.get(role.cls, 2))
    if role.cls == 'plain':
        return role.lead + deeper + (glyph + ' ' if glyph else '')
    if role.cls in NUMBERED:
        if glyph and gcls == role.cls and gcls in ('circnum', 'roman') and role.glyph:
            k = _number_of(glyph)
            if k:
                return role.lead + auto_number(gcls, k, role.glyph) + (role.trail or ' ')
        if glyph and (gcls == role.cls or gcls in NUMBERED and not tag):
            return role.lead + glyph + (role.trail or ' ')
        if tag or not glyph:
            return role.lead + next_no(role.cls, role.glyph) + (role.trail or ' ')
        return role.lead + deeper + glyph + ' '
    # 기호(□ ○ - ※ 등)가 있는 견본
    if tag or want == role.cls:
        return role.lead + role.glyph + role.trail
    if not glyph:
        return role.lead + ' ' * (len(role.glyph) + len(role.trail) + 1)
    return role.lead + deeper + glyph + (role.trail or ' ')


def _nospace(s):
    return re.sub(r'\s+', '', s)


def align_outline(doc, items, frame_end):
    """개요 줄을 양식 본문 줄과 짝짓는다(diff 방식). {개요 번호: (방식, 원본 블록들, 자리, 줄 수가 같은가)}
    'same' = 안 고친 줄(원본 줄을 그대로 옮긴다), 'near' = 고친 자리의 줄(그 자리 원본 줄 모양을 견본으로 쓴다)."""
    orig, new = [], []
    for b in doc.blocks[frame_end:]:
        if b.kind in ('text', 'tablehead'):
            orig.append((b.i, _nospace(b.text)))
        elif b.kind == 'shapehead':
            orig.append((b.i, _nospace(b.text[b.a:])))
        elif b.kind == 'table':
            orig.append((b.i, '\x00표'))
        elif b.kind == 'object':
            orig.append((b.i, '\x00원본%d' % b.i))
    for k, it in enumerate(items):
        if it[0] == 'text':
            new.append((k, _nospace(it[2])))
        elif it[0] == 'table':
            new.append((k, '\x00표'))
        elif it[0] == 'orig':
            new.append((k, '\x00원본%d' % it[1]))
    sm = difflib.SequenceMatcher(None, [x[1] for x in orig], [x[1] for x in new], autojunk=False)
    hints = {}
    for op, i1, i2, j1, j2 in sm.get_opcodes():
        if op == 'equal':
            for d in range(i2 - i1):
                hints[new[j1 + d][0]] = ('same', [orig[i1 + d][0]], 0, True)
        elif op == 'replace':
            pool = [orig[i][0] for i in range(i1, i2)]
            for j in range(j1, j2):
                hints[new[j][0]] = ('near', pool, j - j1, i2 - i1 == j2 - j1)
    return hints


def _role_from(role, b):
    """같은 종류의 다른 원본 줄 b를 견본으로 쓰는 역할(앞 공백·문단 모양·본문 글자 모양은 b의 것)."""
    v = copy.copy(role)
    v.ex = b.i
    v.lead, v.trail = b.lead, b.trail
    v.a, v.b = b.a, b.b
    if b.label:
        v.sep = b.label[1]
    if b.body_cp:
        v.body_cp = b.body_cp
    return v


def restyle_like(p, orig):
    """고친 줄 p의 글자마다 짝지은 원본 줄 orig의 같은 자리 글자 모양을 입힌다.
    「… 위한 2026학년도 장학생 …」처럼 줄의 일부만 굵게 한 강조가, 날짜만 고쳐도 사라지지 않게 한다.
    원본 줄의 글자 모양이 하나뿐이거나, 글자 말고 다른 요소(탭·조판 부호·개체)가 섞였거나, 많이 고친 줄은 그대로 둔다."""
    def plain(el):
        runs = para_runs(el)
        return bool(runs) and all(len(c) == 0 for r in runs for c in r if c.tag == P('t')) \
            and not any(run_has_control(r) for r in runs)
    if not (plain(orig) and plain(p)):
        return
    src = [(ch, r.get('charPrIDRef')) for r in para_runs(orig) for t in run_ts(r) for ch in (t.text or '')]
    new = ''.join(t.text or '' for r in para_runs(p) for t in run_ts(r))
    if len({c for _, c in src}) < 2 or not new:
        return
    sm = difflib.SequenceMatcher(None, ''.join(ch for ch, _ in src), new, autojunk=False)
    if sm.ratio() < 0.6:
        return
    cps = [None] * len(new)
    for op, i1, i2, j1, j2 in sm.get_opcodes():
        if op == 'equal':
            for k in range(j2 - j1):
                cps[j1 + k] = src[i1 + k][1]
        elif op == 'replace':
            for k in range(j2 - j1):
                cps[j1 + k] = src[i1 + k * (i2 - i1) // (j2 - j1)][1]
    for k in range(len(cps)):            # 끼워 넣은 글자는 바로 앞 글자 모양(맨 앞이면 뒤 글자)
        if cps[k] is None and k > 0:
            cps[k] = cps[k - 1]
    for k in range(len(cps) - 1, -1, -1):
        if cps[k] is None:
            cps[k] = cps[k + 1] if k + 1 < len(cps) else src[-1][1]
    runs = para_runs(p)
    at = list(p).index(runs[0])
    proto = runs[0]
    for r in runs:
        p.remove(r)
    k = 0
    while k < len(new):
        e = k
        while e < len(new) and cps[e] == cps[k]:
            e += 1
        r = copy.deepcopy(proto)
        for c in list(r):
            r.remove(c)
        r.set('charPrIDRef', cps[k])
        etree.SubElement(r, P('t')).text = new[k:e]
        p.insert(at, r)
        at += 1
        k = e


def _copy_line(b, ids):
    """안 고친 줄: 원본 문단을 그대로 옮긴다(섞인 글자 모양·고정폭 빈칸·필드까지). 머리말·쪽 번호 설정만 뺀다."""
    p = copy.deepcopy(b.el)
    for r in para_runs(p):
        for c in list(r):
            ln = local(c.tag)
            if ln == 'secPr' or (ln == 'ctrl' and any(local(cc.tag) in SETUP_CTRL or local(cc.tag) == 'colPr'
                                                      for cc in c)):
                r.remove(c)
        if len(r) == 0 and len(para_runs(p)) > 1:
            p.remove(r)
    for a in ('pageBreak', 'columnBreak'):
        if p.get(a) is not None:
            p.set(a, '0')
    ids.renew(p)
    strip_lineseg(p)
    return p


def make_text_block(doc, item, ids, warns, counters, hint=None, used=None):
    _, tag, line, level = item
    lead, glyph, trail, rest = split_marker(line)
    glyph = glyph.strip()
    if tag and glyph and marker_class(glyph) not in NUMBERED:
        glyph, rest = '', line.strip()  # [소제목] 뒤의 □ ○ 같은 기호는 양식 모양으로 바꾼다
    lab = split_label(rest)
    labeled = bool(lab)
    found = resolve_role(doc, tag, glyph, labeled, rest, level)
    if not found:
        return None, 'plain'
    role, exact = found
    if tag == '소제목' and not exact:
        want = '[소제목]' if level <= 1 else '[소제목%d]' % level
        warns.append('%s 견본이 양식에 없어 %s 견본으로 만들었습니다.' % (want, role.display()))
    head = role.cls in ('tablehead', 'shape')
    same = paired = None
    if hint and used is not None:
        # 같은 종류(줄 머리)라도 원본 줄마다 들여쓰기·글자 크기·위아래 간격이 다르므로, 짝지은 원본 줄을 견본으로 쓴다
        mode, pool, pos, even = hint
        kind = {'tablehead': 'tablehead', 'shape': 'shapehead'}.get(role.cls, 'text')

        def fits(i):
            return doc.blocks[i].kind == kind and doc.blocks[i].key == role.key and i not in used
        if mode == 'same' and fits(pool[0]):
            used.add(pool[0])
            if not head:
                make_prefix(role, tag, glyph, counters)  # 번호 세기는 새로 만든 줄과 똑같이
                return _copy_line(doc.blocks[pool[0]], ids), role.key
            # 제목 상자는 번호를 새로 센 결과까지 원본과 같을 때만 그대로 옮긴다(아래 _same_head)
            same = pool[0]
            role = _role_from(role, doc.blocks[same])
        if mode == 'near':
            src = pool[pos] if (even and fits(pool[pos])) else None
            if src is None:
                nl, br = _nospace(line), 0.0
                for i in pool:
                    if fits(i):
                        r = difflib.SequenceMatcher(None, _nospace(doc.blocks[i].text), nl, autojunk=False).ratio()
                        if r > br:
                            src, br = i, r
                if br < 0.45:
                    src = None
            if src is not None:
                used.add(src)
                role = _role_from(role, doc.blocks[src])
                paired = src
    p = copy.deepcopy(doc.blocks[role.ex].el)
    remove_ctrls(p)
    for a in ('pageBreak', 'columnBreak'):
        if p.get(a) is not None:
            p.set(a, '0')
    new_prefix = make_prefix(role, tag, glyph, counters)
    if role.cls == 'tablehead':
        cells = [tc for tr in first_table(p).findall(P('tr')) for tc in tr.findall(P('tc'))]
        if role.numcell is not None and max(role.numcell, role.textcell) < len(cells):
            # 「Ⅰ | 추진 배경」처럼 번호 칸이 따로 있는 제목 표
            k = _number_of(glyph) or (int(glyph.rstrip('.)')) if glyph.rstrip('.)').isdigit() else 0)
            if not k:
                k, rest = lead_number(rest)
            if k:
                counters[role.key] = k
            else:
                counters[role.key] = counters.get(role.key, 0) + 1
                k = counters[role.key]
            set_cell_text(cells[role.numcell], format_number(role.numfmt, k) + ('.' if role.numdot else ''))
            set_cell_text(cells[role.textcell], rest.strip())
        else:
            set_cell_text(cells[min(role.textcell, len(cells) - 1)], new_prefix + rest.strip())
        try:
            fit_head_box(doc, p, role)
        except Exception:
            pass  # 너비 맞추기는 보기 좋게 하는 일이라, 못 해도 견본 너비 그대로 만든다
        ids.renew(p)
        strip_lineseg(p)
        return _same_head(doc, p, same, ids), role.key
    # 항목명 : 내용
    if lab and role.labeled:
        new_label = lab[0] + role.sep
        body = lab[2]
    else:
        new_label = ''
        body = rest
    fill_para(p, role.a, role.b, new_prefix, new_label, body, role.body_cp)
    if paired is not None and role.cls != 'shape':
        restyle_like(p, doc.blocks[paired].el)  # 짝지은 원본 줄의 부분 강조(굵게 등)를 글자 자리대로 이어받는다
    # 도형 안 번호(①, Ⅰ 등) 자동 증가
    if role.cls == 'shape' and role.numfmt:
        counters[role.key + '#n'] = counters.get(role.key + '#n', 0) + 1
        for r in para_runs(p):
            for c in r:
                if local(c.tag) in OBJ_LOCAL:
                    for t in c.iter(P('t')):
                        if t_text(t).strip():
                            set_t(t, format_number(role.numfmt, counters[role.key + '#n']))
    ids.renew(p)
    strip_lineseg(p)
    want = 'shape' if tag else marker_class(glyph)
    heading_ok = (tag or want in HEAD_CLASSES) and role.cls in HEAD_CLASSES
    if not exact and not heading_ok:
        want = '[%s]' % tag if tag else (glyph or '(기호 없는 본문)')
        warns.append('"%s" 줄 머리는 양식에 없어 %s 견본으로 만들었습니다.' % (want, role.display()))
    return _same_head(doc, p, same, ids), role.key


def _same_head(doc, p, same, ids):
    """안 고친 제목 상자: 새로 만든 상자의 글자(번호 포함)가 원본과 같으면 원본 상자를 그대로 옮긴다."""
    if same is None:
        return p
    o = doc.blocks[same].el
    if _nospace(''.join(t_text(t) for t in p.iter(P('t')))) != _nospace(''.join(t_text(t) for t in o.iter(P('t')))):
        return p
    return _copy_line(doc.blocks[same], ids)


def _doc_gauge(doc):
    """양식 글꼴 폭 비율을 맞춘 쪽 어림 도구(한 번만 만든다). 제목 상자 글자 폭을 잴 때 쓴다."""
    g = getattr(doc, '_gauge', None)
    if g is None:
        g = doc._gauge = PageGauge(doc.pkg.xml('Contents/header.xml'), [doc.root])
        doc._body_w = body_width(list(doc.root))
    return g


def _cell_line_w(tc, g):
    """칸 안에서 가장 긴 줄의 글자 폭(HWPUNIT 어림)."""
    sub = tc.find(P('subList'))
    best = 0.0
    for q in (sub.findall(P('p')) if sub is not None else []):
        w = [0.0]
        for r in para_runs(q):
            cid = r.get('charPrIDRef')
            for t in run_ts(r):
                for ch in t_text(t):
                    if ch == '\n':
                        w.append(0.0)
                    else:
                        w[-1] += g.width(ch, cid)
        best = max(best, max(w))
    return best * g.k


def _cell_margin(tc):
    """칸 안 왼쪽 + 오른쪽 여백(HWPUNIT)."""
    tbl = _ancestor(tc, 'tbl')
    m = tc.find(P('cellMargin')) if tc.get('hasMargin') == '1' else (tbl.find(P('inMargin')) if tbl is not None else None)
    try:
        return int(m.get('left')) + int(m.get('right'))
    except (AttributeError, TypeError, ValueError):
        return 282


def _cell_w(tc):
    return int(tc.find(P('cellSz')).get('width'))


def _resize_cells(tbl, cells, widths):
    """한 줄짜리 표의 칸 너비를 바꾸고 표 너비를 칸 너비 합으로 맞춘다."""
    for tc, w in zip(cells, widths):
        tc.find(P('cellSz')).set('width', str(int(w)))
    tsz = tbl.find(P('sz'))
    if tsz is not None:
        tsz.set('width', str(int(sum(_cell_w(tc) for tc in cells))))


def fit_head_box(doc, p, role):
    """제목 상자(한 줄 표) 너비를 새 글자에 맞춘다.
    - 번호 칸: 새 번호(Ⅷ 등)가 양식이 이미 담은 가장 긴 번호보다 길면, 그 비율만큼 글 칸에서 가져와 번호 칸을 넓힌다.
    - 글 칸: 양식에서 같은 상자의 너비가 글자마다 다르면(글자에 맞춘 상자) 양식 상자들의 「글자 폭 → 너비」 관계를
      따라 새 글자 폭에 맞춰 넓히거나 좁힌다(쪽 본문 너비까지). 너비가 모두 같은 상자(쪽 너비 띠 등)는 글 칸 너비를 그대로 둔다.
    원본과 글자가 같은 상자는 _same_head가 원본 상자를 그대로 옮기므로 너비도 원본 그대로다."""
    tbl = first_table(p)
    src = first_table(doc.blocks[role.ex].el)
    if tbl is None or src is None or len(tbl.findall(P('tr'))) != 1 or len(src.findall(P('tr'))) != 1:
        return
    cells = tbl.find(P('tr')).findall(P('tc'))
    scells = src.find(P('tr')).findall(P('tc'))
    if len(cells) != len(scells) or not cells or any(tc_span(tc) != (1, 1) for tc in cells):
        return
    g = _doc_gauge(doc)
    ti = min(role.textcell, len(cells) - 1)
    widths = [_cell_w(tc) for tc in cells]
    # 양식에 있는 같은 상자들(칸 수가 같은 것)
    peers = []
    for b in doc.blocks:
        t = first_table(b.el) if b.kind == 'tablehead' and b.key == role.key else None
        tr = t.find(P('tr')) if t is not None else None
        if tr is not None and len(tr.findall(P('tc'))) == len(cells):
            peers.append(tr.findall(P('tc')))
    ni = role.numcell
    if ni is not None and ni < len(cells) and ni != ti:
        # 번호 칸: 양식이 이미 담고 있는 가장 긴 번호(III·붙임 등)보다 길 때만, 그 비율만큼 넓힌다
        nw = _cell_line_w(cells[ni], g)
        fit = [(_cell_line_w(c[ni], g), _cell_w(c[ni]) - _cell_margin(c[ni])) for c in peers]
        fit = [(w, room) for w, room in fit if w > 0 and room > 0]
        if fit:
            w0, room0 = max(fit)
            need = int(math.ceil(room0 * nw / w0)) + _cell_margin(cells[ni]) - widths[ni] if nw > w0 + 50 else 0
            spare = widths[ti] - _cell_line_w(cells[ti], g) - _cell_margin(cells[ti])
            if 0 < need < spare:
                widths[ni] += need
                widths[ti] -= need
    if len({_cell_w(c[ti]) for c in peers}) >= 2:
        # 글 칸: 양식 상자들의 「글자 폭 → 상자 너비」를 직선으로 맞춰 새 글자 폭의 너비를 정한다
        # (양식마다 글자가 늘 때 상자를 넓히는 정도가 달라서, 여유 폭을 하나로 두면 원본 상자와 어긋난다)
        pts = [(_cell_line_w(c[ti], g), _cell_w(c[ti])) for c in peers]
        pts = [(x, y) for x, y in pts if x > 0]
        xs = [x for x, _ in pts]
        if len(set(round(x) for x in xs)) >= 3:
            mx, my = statistics.mean(xs), statistics.mean(y for _, y in pts)
            slope = sum((x - mx) * (y - my) for x, y in pts) / sum((x - mx) ** 2 for x in xs)
            slope = max(1.0, min(3.0, slope))
        else:
            mx, my, slope = statistics.median(xs), statistics.median(y for _, y in pts), 1.0
        tw = _cell_line_w(cells[ti], g)
        if tw > 0:
            room = (getattr(doc, '_body_w', 0) or sum(widths)) - (sum(widths) - widths[ti])
            want = max(my + slope * (tw - mx), tw + _cell_margin(cells[ti]) + 200, 1000)
            if abs(want - widths[ti]) >= 100:
                widths[ti] = int(round(min(want, max(room, widths[ti]))))
    if widths != [_cell_w(tc) for tc in cells]:
        _resize_cells(tbl, cells, widths)


def _col_widths(rows, C, W, ex_widths):
    if ex_widths and len(ex_widths) == C:
        return list(ex_widths)
    w = []
    for j in range(C):
        if any(j < len(r) and PHOTO_RE.match(r[j] or '') for r in rows):
            w.append(24)  # 사진 칸이 든 열은 설명 글 길이와 상관없이 같은 너비
            continue
        mx = max([disp_len(max((r[j] if j < len(r) else '').split('\n'), key=disp_len)) for r in rows] + [2])
        w.append(min(max(mx, 3), 24))
    tot = sum(w)
    out = [int(W * x / tot) for x in w]
    out[-1] += W - sum(out)
    return out


def set_cell_text(tc, text, para_pr=None):
    """표 칸 글자를 바꾼다. n번째 줄은 원래 칸의 n번째 문단 모양을 따르고(넘치면 마지막 문단 모양),
    'Ⅰ. 제목'처럼 번호와 글자 모양이 다르면 번호는 번호 자리, 글은 글 자리에 넣는다."""
    sub = tc.find(P('subList'))
    if sub is None:
        return
    ps = sub.findall(P('p'))
    if not ps:
        return
    if re.sub(r'\s', '', '\n'.join(para_text(x) for x in ps)) == re.sub(r'\s', '', text or ''):
        # 글자가 그대로인 칸은 손대지 않는다(계산식·섞인 글자 모양·고정폭 빈칸 유지)
        if para_pr:
            for x in ps:
                x.set('paraPrIDRef', para_pr)
        return
    for x in ps:
        for fb in x.iter(P('fieldBegin')):
            if fb.get('type') == 'FORMULA' and '\n' not in (text or ''):
                # 합계 같은 계산식 칸: 식은 그대로 두고 보이는 값만 바꾼다
                segs, n = t_segments(x)
                order = list(x.iter())
                first_t = next((e for e in order[order.index(fb):] if e.tag == P('t')), None)
                seg = next((sg for sg in segs if sg[1] is first_t), segs[0] if segs else None)
                fill_para(x, 0, 0, '', '', text or '', body_seg=seg)
                if is_numeric(text or ''):
                    for prm in fb.iter(P('stringParam')):
                        if prm.get('name') == 'LastResult':
                            prm.text = text.strip()
                        elif prm.get('name') == 'Command' and ';;' in (prm.text or ''):
                            prm.text = prm.text.rsplit(';;', 1)[0] + ';;' + text.strip()
                for y in ps:
                    if y is not x:
                        sub.remove(y)
                if para_pr:
                    x.set('paraPrIDRef', para_pr)
                return
    styles = [x for x in ps if para_text(x).strip()] or ps[:1]
    for x in ps:
        sub.remove(x)
    for i, ln in enumerate(text.split('\n') if text else ['']):
        ex = styles[min(i, len(styles) - 1)]
        np_ = copy.deepcopy(ex)
        remove_ctrls(np_, keep_objects=False)
        el, eg, et, er = split_marker(para_text(ex))
        a = len(el) + len(eg) + len(et)
        nl, ng, nt, nr = split_marker(ln)
        if eg and ng:
            fill_para(np_, a, a, nl + ng + nt, '', nr)
        elif eg:
            fill_para(np_, a, a, '', '', ln)
        else:
            fill_para(np_, 0, 0, '', '', ln)
        if para_pr:
            np_.set('paraPrIDRef', para_pr)
        sub.append(np_)


PHOTO_RE = re.compile(r'^\s*\[\s*사진\s*\d*\s*\]\s*$')  # 표 칸의 사진 자리. build·fill이 [사진1]처럼 번호를 붙인다
PHOTO_MIN = (5600, 4200)  # 이보다 큰 그림만 든 칸을 사진 칸으로 본다(약 20×15mm, 작은 로고·도장 제외)


SEQ_RE = re.compile(r'^\s*(\d+|\d+\s*(회|차|주|월|일|기|번|위)(차)?|[①-⑳]|[가나다라마바사아자차카타파하]\.?|합\s*계|소\s*계|계|총\s*계|\d{1,2}\.\s*\d{1,2}\.?.*)\s*$')


def data_table(t):
    """머리 줄 아래 첫 칸이 차례(1, 1회, ①, 9. 15. 등)인 꽉 찬 표: 실적·일정 같은 자료 표라서 칸 채우는 서식으로 보지 않는다."""
    if not t['header'] or t['filled'] < 0.7:
        return False
    col0 = [r[0].strip() for r in t['grid'][1:] if r]
    return len(col0) >= 3 and sum(1 for c in col0 if SEQ_RE.match(c)) >= max(3, (len(col0) + 1) // 2)


def photo_cell(tc):
    """글자 없이 큰 그림만 든 표 칸(사진 칸)인가."""
    if tc_text(tc).strip():
        return False
    for e in tc.iter(P('pic')):
        sz = e.find(P('sz'))
        try:
            if int(sz.get('width')) >= PHOTO_MIN[0] and int(sz.get('height')) >= PHOTO_MIN[1]:
                return True
        except Exception:
            pass
    return False


def number_photos(cells, start):
    """칸 글자 목록에서 [사진] 자리에 차례 번호를 붙인다. (새 목록, 다음 번호)"""
    out = []
    for c in cells:
        if PHOTO_RE.match(c or ''):
            start += 1
            c = '[사진%d]' % start
        out.append(c)
    return out, start


def photo_frames(tbl, hed=None):
    """사진 자리가 든 줄은 칸이 납작하면 사진 비율(4:3)이 되도록 높이를 늘린다. 늘린 줄 수를 돌려준다.
    hed가 있으면 사진 자리 문단을 글머리표 없는 가운데 정렬로 바꾼다(양식 칸의 '▸' 같은 글머리표가 사진 앞에 남지 않게)."""
    n = 0
    for tr in tbl.findall(P('tr')):
        tcs = tr.findall(P('tc'))
        slots = [tc for tc in tcs if re.fullmatch(r'\[사진\d+\]', tc_text(tc).strip())]
        if not slots:
            continue
        if hed is not None:
            for tc in slots:
                for x in _tc_paras(tc):
                    x.set('paraPrIDRef', hed.photo_para(x.get('paraPrIDRef')))
        want = max(int(tc_size(tc)[0] * 0.75) for tc in slots)
        if all(tc_size(tc)[1] >= want * 0.7 for tc in slots):
            continue
        for tc in tcs:
            sz = tc.find(P('cellSz'))
            if sz is not None and tc_span(tc)[1] == 1 and int(sz.get('height', '0') or 0) < want:
                sz.set('height', str(want))
        n += 1
    if n:
        total = sum(max([tc_size(tc)[1] for tc in tr.findall(P('tc')) if tc_span(tc)[1] == 1] + [0])
                    for tr in tbl.findall(P('tr')))
        sz = tbl.find(P('sz'))
        if sz is not None and total:
            sz.set('height', str(max(total, int(sz.get('height', '0') or 0))))
    return n


NUMERIC_RE = re.compile(r'[\d\s,.%~\-+()/:·원명개건회차시분초년월일주천만억$₩]*')


def is_numeric(s):
    s = s.strip()
    return bool(s) and bool(re.search(r'\d', s)) and bool(NUMERIC_RE.fullmatch(s))


class HeaderEditor:
    """header.xml 에 테두리 정의를 '덧붙이기만' 한다(기존 정의는 건드리지 않음)."""

    def __init__(self, pkg):
        self.pkg = pkg
        self.root = None
        self.cache = {}
        self.dirty = False

    def _load(self):
        if self.root is None:
            self.root = self.pkg.xml('Contents/header.xml')
            self.bfs = self.root.find('.//' + H('borderFills'))
            self.by_id = {b.get('id'): b for b in self.bfs.findall(H('borderFill'))}

    def side(self, bf_id, side):
        self._load()
        b = self.by_id.get(bf_id)
        e = b.find(H(side + 'Border')) if b is not None else None
        return (e.get('type'), e.get('width'), e.get('color')) if e is not None else None

    def _append(self, nb, key):
        new_id = str(max(int(i) for i in self.by_id) + 1)
        nb.set('id', new_id)
        self.bfs.append(nb)
        self.by_id[new_id] = nb
        self.bfs.set('itemCnt', str(len(self.by_id)))
        self.cache[key] = new_id
        self.dirty = True
        return new_id

    def variant(self, bf_id, **sides):
        """bf_id 테두리에서 top/bottom 등 일부 선만 바꾼 정의의 번호."""
        self._load()
        base = self.by_id.get(bf_id)
        if base is None:
            return bf_id
        changes = tuple(sorted((k, v) for k, v in sides.items() if v and self.side(bf_id, k) != v))
        if not changes:
            return bf_id
        key = (bf_id, changes)
        if key in self.cache:
            return self.cache[key]
        nb = copy.deepcopy(base)
        for k, (t, w, c) in changes:
            e = nb.find(H(k + 'Border'))
            e.set('type', t)
            e.set('width', w)
            e.set('color', c)
        return self._append(nb, key)

    def simple(self, fill):
        """사방 검은 실선(+배경색) 테두리 정의 — 양식에 표가 없을 때만 쓴다."""
        self._load()
        key = ('simple', fill)
        if key in self.cache:
            return self.cache[key]
        nb = copy.deepcopy(self.bfs.find(H('borderFill')))
        for s in ('left', 'right', 'top', 'bottom'):
            e = nb.find(H(s + 'Border'))
            if e is None:
                e = etree.SubElement(nb, H(s + 'Border'))
            e.set('type', 'SOLID')
            e.set('width', '0.12 mm')
            e.set('color', '#000000')
        for fb in nb.findall(C('fillBrush')):
            nb.remove(fb)
        if fill:
            fb = etree.SubElement(nb, C('fillBrush'))
            wb = etree.SubElement(fb, C('winBrush'))
            wb.set('faceColor', fill)
            wb.set('hatchColor', '#999999')
            wb.set('alpha', '0')
        return self._append(nb, key)

    def dark_fill(self, bf_id):
        """칸 바탕이 어두운 색인지(흰 글자·연한 글자가 일부러 쓰인 칸)."""
        self._load()
        b = self.by_id.get(bf_id)
        wb = b.find('.//' + C('winBrush')) if b is not None else None
        lum = color_lum(wb.get('faceColor')) if wb is not None else None
        return lum is not None and lum < 0.5

    def ink_char(self, cid):
        """연한 회색(안내 글자용) 글자 모양이면, 같은 모양에 글자색만 검정으로 바꾼 정의의 번호."""
        self._load()
        if not hasattr(self, 'cps'):
            self.cps = self.root.find('.//' + H('charProperties'))
            self.cp_by_id = {c.get('id'): c for c in self.cps.findall(H('charPr'))} if self.cps is not None else {}
        c = self.cp_by_id.get(cid)
        lum = color_lum(c.get('textColor')) if c is not None else None
        if lum is None or not 0.6 < lum < 0.97:
            return cid
        key = ('ink', cid)
        if key in self.cache:
            return self.cache[key]
        nc = copy.deepcopy(c)
        nc.set('textColor', '#000000')
        new_id = str(max(int(i) for i in self.cp_by_id) + 1)
        nc.set('id', new_id)
        self.cps.append(nc)
        self.cp_by_id[new_id] = nc
        self.cps.set('itemCnt', str(len(self.cp_by_id)))
        self.cache[key] = new_id
        self.dirty = True
        return new_id

    def photo_para(self, pp_id):
        """사진 자리 문단 모양: 같은 모양에서 글머리표·번호·여백·문단 위아래 간격을 없애고 가운데 정렬한 정의의 번호."""
        self._load()
        if not hasattr(self, 'pps'):
            self.pps = self.root.find('.//' + H('paraProperties'))
            self.pp_by_id = {x.get('id'): x for x in self.pps.findall(H('paraPr'))} if self.pps is not None else {}
        b = self.pp_by_id.get(pp_id)
        if b is None:
            return pp_id
        key = ('photo', pp_id)
        if key in self.cache:
            return self.cache[key]
        nb = copy.deepcopy(b)
        hd = nb.find(H('heading'))
        if hd is not None:
            hd.set('type', 'NONE')
            hd.set('idRef', '0')
            hd.set('level', '0')
        al = nb.find(H('align'))
        if al is not None:
            al.set('horizontal', 'CENTER')
        for m in nb.iter(H('margin')):
            for k in ('intent', 'left', 'right', 'prev', 'next'):
                e = m.find(C(k))
                if e is not None:
                    e.set('value', '0')
        if etree.tostring(nb) == etree.tostring(b):
            self.cache[key] = pp_id
            return pp_id
        new_id = str(max(int(i) for i in self.pp_by_id) + 1)
        nb.set('id', new_id)
        self.pps.append(nb)
        self.pp_by_id[new_id] = nb
        self.pps.set('itemCnt', str(len(self.pp_by_id)))
        self.cache[key] = new_id
        self.dirty = True
        return new_id

    def seam_para(self, pp_id, keep_prev):
        """나눈 사진 표를 담은 문단 모양: 줄 간격 100%(표 아래에 덧붙는 줄 간격을 없앰), keep_prev가 아니면 문단 위 간격도 0.
        이어지는 사진 표 사이가 벌어지지 않고 한 표처럼 붙어 보이게 한다."""
        self._load()
        if not hasattr(self, 'pps'):
            self.pps = self.root.find('.//' + H('paraProperties'))
            self.pp_by_id = {x.get('id'): x for x in self.pps.findall(H('paraPr'))} if self.pps is not None else {}
        b = self.pp_by_id.get(pp_id)
        if b is None:
            return pp_id
        key = ('seam', pp_id, keep_prev)
        if key in self.cache:
            return self.cache[key]
        nb = copy.deepcopy(b)
        for ls in nb.iter(H('lineSpacing')):
            if ls.get('type') == 'PERCENT':
                ls.set('value', '100')
        if not keep_prev:
            for m in nb.iter(H('margin')):
                e = m.find(C('prev'))
                if e is not None:
                    e.set('value', '0')
        if etree.tostring(nb) == etree.tostring(b):
            self.cache[key] = pp_id
            return pp_id
        new_id = str(max(int(i) for i in self.pp_by_id) + 1)
        nb.set('id', new_id)
        self.pps.append(nb)
        self.pp_by_id[new_id] = nb
        self.pps.set('itemCnt', str(len(self.pp_by_id)))
        self.cache[key] = new_id
        self.dirty = True
        return new_id

    def keep_next(self, pp_id):
        """같은 문단 모양에 '다음 문단과 함께'만 켠 정의의 번호(이미 켜져 있으면 그대로)."""
        self._load()
        if not hasattr(self, 'pps'):
            self.pps = self.root.find('.//' + H('paraProperties'))
            self.pp_by_id = {x.get('id'): x for x in self.pps.findall(H('paraPr'))} if self.pps is not None else {}
        b = self.pp_by_id.get(pp_id)
        bs = b.find(H('breakSetting')) if b is not None else None
        if bs is None or bs.get('keepWithNext') == '1':
            return pp_id
        key = ('keep', pp_id)
        if key in self.cache:
            return self.cache[key]
        nb = copy.deepcopy(b)
        nb.find(H('breakSetting')).set('keepWithNext', '1')
        new_id = str(max(int(i) for i in self.pp_by_id) + 1)
        nb.set('id', new_id)
        self.pps.append(nb)
        self.pp_by_id[new_id] = nb
        self.pps.set('itemCnt', str(len(self.pp_by_id)))
        self.cache[key] = new_id
        self.dirty = True
        return new_id

    def save(self):
        if self.dirty:
            self.pkg.put_xml('Contents/header.xml', self.root)


def content_table(p):
    """문단 바로 아래에 있는 내용 표(두 줄 이상이거나 사진 자리가 있는 표). 한 줄짜리 제목 상자는 뺀다."""
    for r in para_runs(p):
        for c in r:
            if local(c.tag) != 'tbl':
                continue
            if int(c.get('rowCnt') or 0) >= 2 or any(PHOTO_RE.match(t.text or '') for t in c.iter(P('t'))):
                return c
    return None


def keep_with_tables(blocks, start, hed):
    """표 바로 앞 제목·안내 줄에 '다음 문단과 함께'를 켠다(사이의 빈 줄 포함).
    글자처럼 취급한 표는 쪽 끝에 다 들어가지 않으면 통째로 다음 쪽으로 넘어가서, 앞의 제목만 쪽 끝에 홀로 남는다."""
    for i in range(max(start, 1), len(blocks)):
        if content_table(blocks[i]) is None:
            continue
        j = i - 1
        while j >= start and content_table(blocks[j]) is None:
            p = blocks[j]
            p.set('paraPrIDRef', hed.keep_next(p.get('paraPrIDRef')))
            if para_text(p).strip() or has_inline_obj(p):
                break
            j -= 1


def keep_headings(blocks, emitted, heads, box_keys, hed):
    """제목(상자·짧은 제목 줄)과 바로 뒤 빈 줄에 '다음 문단과 함께'를 켠다. 쪽 끝에 제목만 남고 내용이 다음 쪽으로 가지 않게.
    같은 종류 줄이 이어지는 목록(1. 2. 3. …)은 마지막 줄만, 다음 블록이 새 쪽에서 시작하면 켜지 않는다."""
    pos = {id(b): i for i, b in enumerate(blocks)}
    for j, (el, key) in enumerate(emitted[:-1]):
        if key not in heads:
            continue
        nxt_el, nxt = emitted[j + 1]
        if nxt_el.get('pageBreak') == '1':
            continue
        if key not in box_keys and (nxt == key or len(para_text(el).strip()) > 40):
            continue
        i = pos.get(id(el))
        if i is None:
            continue
        k = i
        while k < len(blocks) and (k == i or (not para_text(blocks[k]).strip() and not has_inline_obj(blocks[k])
                                               and blocks[k].get('pageBreak') != '1')):
            blocks[k].set('paraPrIDRef', hed.keep_next(blocks[k].get('paraPrIDRef')))
            k += 1


def body_height(blocks):
    """쪽 본문 높이(HWPUNIT): 용지 높이 - 위·아래 여백 - 머리말·꼬리말 여백. 찾지 못하면 0."""
    for b in blocks:
        for pp in b.iter(P('pagePr')):
            try:
                h = int(pp.get('width') if pp.get('landscape') == 'NARROWLY' else pp.get('height'))
                m = pp.find(P('margin'))
                if m is not None:
                    h -= sum(int(m.get(k, '0') or 0) for k in ('top', 'bottom', 'header', 'footer'))
                return max(0, h)
            except (TypeError, ValueError):
                return 0
    return 0


def body_width(blocks):
    """쪽 본문 너비(HWPUNIT): 용지 너비 - 왼쪽·오른쪽·제본 여백. 찾지 못하면 0."""
    for b in blocks:
        for pp in b.iter(P('pagePr')):
            try:
                w = int(pp.get('height') if pp.get('landscape') == 'NARROWLY' else pp.get('width'))
                m = pp.find(P('margin'))
                if m is not None:
                    w -= sum(int(m.get(k, '0') or 0) for k in ('left', 'right', 'gutter'))
                return max(0, w)
            except (TypeError, ValueError):
                return 0
    return 0


PHOTO_ROOM = 10000  # 사진 표 앞 제목·여백 몫(약 3.5cm). 나눈 표 하나는 쪽 본문 높이에서 이만큼 뺀 높이까지


def split_photo_tables(blocks, start, ids, warns, hed=None):
    """사진 자리 표를 묶음(사진 줄 + 그 아래 설명 줄)마다 따로 표로 나눈다. 글자처럼 취급한 표는 쪽을 넘겨 나뉘지 않아,
    한 표로 두면 쪽 끝에 다 들어가지 않을 때 표 전체가 다음 쪽으로 넘어가 앞 쪽 아래가 크게 비고(한 쪽보다 길면 아래가 잘림),
    묶음마다 나누면 들어가는 묶음까지는 앞 쪽에 남는다. 나뉜 표끼리는 사이를 붙여 한 쪽 안에서는 한 표처럼 보이게 한다."""
    limit = body_height(blocks) - PHOTO_ROOM
    if limit <= 0:
        return
    out = blocks[:start]
    for b in blocks[start:]:
        parts = _split_photo(b, limit, ids, hed)
        if parts is None:
            out.append(b)
        elif parts == 'span':
            warns.append('사진 자리 표가 한 쪽보다 길지만 여러 줄을 합친 칸이 있어 나누지 못했습니다. 한글에서 아래가 잘릴 수 있으니 '
                         '사진 줄 2~3개씩 표를 나눠 쓰세요.')
            out.append(b)
        else:
            out.extend(parts)
    blocks[:] = out


def _split_photo(p, limit, ids, hed=None):
    tbls = [c for r in para_runs(p) for c in r if c.tag == P('tbl')]
    if len(tbls) != 1:
        return None
    tbl = tbls[0]
    pos = tbl.find(P('pos'))
    if pos is None or pos.get('treatAsChar') != '1':
        return None  # 글자처럼 취급하지 않은 표는 한글이 쪽 경계에서 나눈다
    trs = tbl.findall(P('tr'))
    photo = [any(re.fullmatch(r'\[사진\d+\]', tc_text(tc).strip()) for tc in tr.findall(P('tc'))) for tr in trs]
    if not any(photo):
        return None
    hs = [max([tc_size(tc)[1] for tc in tr.findall(P('tc')) if tc_span(tc)[1] == 1] + [0]) for tr in trs]
    # 묶음: 사진 줄 + 다음 사진 줄 전까지의 줄. 첫 사진 줄 앞의 줄(제목 줄 등)은 첫 묶음에 붙인다
    first = photo.index(True)
    units = []
    for i in range(first, len(trs)):
        if photo[i] or not units:
            units.append([i])
        else:
            units[-1].append(i)
    units[0] = list(range(first)) + units[0]
    if len(units) < 2:
        return None
    chunks = units  # 묶음 하나씩 따로 표로
    where = {i: k for k, ch in enumerate(chunks) for i in ch}
    for i, tr in enumerate(trs):
        for tc in tr.findall(P('tc')):
            rs = tc_span(tc)[1]
            if rs > 1 and len({where.get(j) for j in range(i, i + rs)}) > 1:
                return 'span' if sum(hs) > limit else None
    out = []
    copies = [p] + [copy.deepcopy(p) for _ in chunks[1:]]  # 줄을 지우기 전에 복사해 둔다
    for k, ch in enumerate(chunks):
        q = copies[k]
        t = q.find('.//' + P('tbl'))
        rows = t.findall(P('tr'))
        for i, tr in enumerate(rows):
            if i not in ch:
                t.remove(tr)
        base = ch[0]
        for tr in t.findall(P('tr')):
            for tc in tr.findall(P('tc')):
                ad = tc.find(P('cellAddr'))
                if ad is not None:
                    ad.set('rowAddr', str(int(ad.get('rowAddr', '0') or 0) - base))
        zl = t.find(P('cellzoneList'))  # 칸 묶음 모양도 이 표에 남은 줄만큼 자르고 번호를 당긴다
        if zl is not None:
            for zn in list(zl):
                s0, e0 = int(zn.get('startRowAddr', '0') or 0), int(zn.get('endRowAddr', '0') or 0)
                if e0 < ch[0] or s0 > ch[-1]:
                    zl.remove(zn)
                    continue
                zn.set('startRowAddr', str(max(s0, ch[0]) - base))
                zn.set('endRowAddr', str(min(e0, ch[-1]) - base))
            if not len(zl):
                t.remove(zl)
        t.set('rowCnt', str(len(ch)))
        sz = t.find(P('sz'))
        if sz is not None:
            sz.set('height', str(sum(hs[i] for i in ch)))
        if k:
            remove_ctrls(q)
            for r in para_runs(q):  # 표 말고 같은 문단에 있던 글자는 첫 표에만 둔다
                for tt in run_ts(r):
                    for c in list(tt):
                        tt.remove(c)
                    tt.text = ''
            for a in ('pageBreak', 'columnBreak'):
                if q.get(a) is not None:
                    q.set(a, '0')
            ids.renew(q)
        # 나뉜 표 사이를 붙인다: 맞닿는 쪽의 바깥 여백, 둘째 표부터 문단 위 간격, 표 아래에 덧붙는 줄 간격을 없앤다
        om = t.find(P('outMargin'))
        if om is not None:
            if k:
                om.set('top', '0')
            if k < len(chunks) - 1:
                om.set('bottom', '0')
        if hed is not None and not para_text(q).strip():
            q.set('paraPrIDRef', hed.seam_para(q.get('paraPrIDRef'), not k))
        strip_lineseg(q)
        out.append(q)
    return out


def color_lum(s):
    """'#RRGGBB' 밝기(0=검정, 1=흰색). 색이 아니면 None."""
    m = re.fullmatch(r'#([0-9A-Fa-f]{6})', s or '')
    if not m:
        return None
    r, g, b = (int(m.group(1)[i:i + 2], 16) / 255.0 for i in (0, 2, 4))
    return 0.299 * r + 0.587 * g + 0.114 * b


def ink_runs(paras, hed):
    """새로 채운 글자가 양식의 연한 안내 글자 모양을 물려받았으면 검은 글자로 바꾼다. 바꾼 run 수."""
    n = 0
    for p in paras:
        for r in para_runs(p):
            if not any(t_text(t).strip() for t in run_ts(r)):
                continue
            cid = r.get('charPrIDRef')
            new = hed.ink_char(cid)
            if new != cid:
                r.set('charPrIDRef', new)
                n += 1
    return n


def _tc_paras(tc):
    sub = tc.find(P('subList'))
    return sub.findall(P('p')) if sub is not None else []


def make_table_block(doc, tno, rows, ids, warns):
    info = doc.tables[tno]
    hed = doc.hedit
    p = copy.deepcopy(doc.blocks[info['block']].el)
    remove_ctrls(p)
    for a in ('pageBreak', 'columnBreak'):
        if p.get(a) is not None:
            p.set(a, '0')
    for r in para_runs(p):
        for t in run_ts(r):
            set_t(t, '')
    tbl = first_table(p)
    trs = tbl.findall(P('tr'))
    R0 = len(trs)
    C0 = max(int(tbl.get('colCnt', '0') or 0), max(len(tr.findall(P('tc'))) for tr in trs))
    counts = [len(tr.findall(P('tc'))) for tr in trs]
    # [사진] 칸에 문서 전체 차례 번호를 붙인다([사진1], [사진2] …). 사진은 '사진 넣기'가 이 자리에 넣는다
    numbered = []
    for r in rows:
        r, doc.photo_n = number_photos(r, doc.photo_n)
        numbered.append(r)
    rows = numbered

    def padded(r, k):
        if len(r) == counts[k]:
            return r
        if len(r) == counts[k] - 1 and not tc_text(trs[k].findall(P('tc'))[-1]).strip():
            return r + ['']  # 「활동주제 | 」처럼 끝의 빈칸이 개요에서 빠진 줄
        return None

    def fit(rs, idx):
        out = [padded(r, k) for r, k in zip(rs, idx)]
        return out if len(rs) == len(idx) and all(x is not None for x in out) else None
    # 글자 없는 줄(사진 칸 등)이 개요에서 빈 줄로 빠져도 양식 자리에 그대로 둔다
    filled = [r for r in rows if any(c.strip() for c in r)]
    keep = [k for k in range(R0) if any(tc_text(tc).strip() for tc in trs[k].findall(P('tc')))]
    same_rows = fit(rows, list(range(R0)))
    if same_rows:
        rows = same_rows
    elif keep and len(keep) < R0 and fit(filled, keep):
        full = [[''] * counts[k] for k in range(R0)]
        for r, k in zip(fit(filled, keep), keep):
            full[k] = r
        rows = full

    # 1) 줄 수와 줄마다 칸 수가 양식과 똑같으면: 병합·폭·테두리 모두 그대로 두고 글자만 바꾼다
    if len(rows) == R0 and all(len(rows[i]) == counts[i] for i in range(R0)):
        for i, tr in enumerate(trs):
            for j, tc in enumerate(tr.findall(P('tc'))):
                set_cell_text(tc, rows[i][j])
        photo_frames(tbl, hed)
        pics = sum(1 for tc in tbl.iter(P('tc')) if photo_cell(tc))
        if pics:
            warns.append('표 %d에 양식의 사진 %d장이 그대로 남아 있습니다. 새 사진을 넣을 자리면 개요의 그 칸을 [사진]으로 쓰세요.'
                         % (tno, pics))
        ids.renew(p)
        strip_lineseg(p)
        return p, 'table%d' % tno
    rows = filled or [['']]
    n = len(rows)

    def clean(tr):
        cs = tr.findall(P('tc'))
        return len(cs) == C0 and all(tc_span(tc) == (1, 1) for tc in cs)
    # 2) 머리 부분(병합 포함)은 그대로 두고, 본문 줄은 깨끗한 견본 줄로 늘이거나 줄인다
    h = 1
    while h < R0 and not clean(trs[h]):
        h += 1
    body_clean = [k for k in range(h, R0) if clean(trs[k])]
    keep_head = (h < R0 and body_clean and n > h and all(len(rows[i]) == counts[i] for i in range(h))
                 and all(len(r) == C0 for r in rows[h:]))
    if keep_head:
        head_rows, body_rows, C = trs[:h], rows[h:], C0
        first_body = h
    else:
        C = max(len(r) for r in rows)
        rows = [r + [''] * (C - len(r)) for r in rows]
        head_rows, body_rows = [], rows[1:]
        first_body = 1
        if any(not clean(tr) for tr in trs):
            warns.append('표 %d의 병합된 칸은 새 표에서 풀었습니다(줄·칸 수가 원래 표와 달라서). '
                         '필요하면 한글에서 다시 합치세요.' % tno)
    ok = [k for k in range(R0) if clean(trs[k])]
    if not ok:
        base_tr = copy.deepcopy(trs[0])
        tc0 = base_tr.findall(P('tc'))[0]
        for tc in base_tr.findall(P('tc')):
            base_tr.remove(tc)
        for j in range(C0):
            base_tr.append(copy.deepcopy(tc0))
        head_ex = mid_ex = last_ex = base_tr
        b_first = b_last = None
    else:
        body_ok = [k for k in ok if k >= h] or [k for k in ok if k > 0] or ok
        mids = [k for k in body_ok if k < R0 - 1 and k > body_ok[0]] or body_ok
        mid_ex = trs[mids[0]]
        last_ex = trs[R0 - 1] if (R0 - 1) in ok else mid_ex
        head_ex = trs[0]
        b_first, b_last = trs[body_ok[0]], last_ex
    # 칸 폭: 깨끗한 본문 줄의 폭이 가장 정확하다
    width_src = mid_ex if clean(mid_ex) else head_ex
    ex_widths = [tc_size(tc)[0] for tc in width_src.findall(P('tc'))]
    W = sum(ex_widths) or int(tbl.find(P('sz')).get('width', '40000'))
    # 같은 표를 다시 쓰는 것(머리 줄이 같음)이면 양식의 칸 폭, 다른 내용의 표면 글자 길이에 맞춘 폭
    def norm(c):
        return re.sub(r'\s', '', c)
    g0 = info['grid'][0] if info['grid'] else []
    same_head = bool(g0) and sum(1 for a, b in zip(rows[0], g0) if norm(a) == norm(b)) * 2 >= len(g0)
    head_clean = keep_head and all(clean(tr) for tr in trs[:h])
    use_ex = C == C0 and (same_head or (keep_head and not head_clean))
    widths = _col_widths(rows if not keep_head else rows[h:], C, W, ex_widths if use_ex else None)

    def colmap(j):
        if C == C0:
            return j
        if j == 0:
            return 0
        if j == C - 1:
            return C0 - 1
        if C0 <= 2:
            return min(1, C0 - 1)
        return 1 + (j - 1) % (C0 - 2)

    # 본문 줄 사이 선(양식에 본문 줄이 둘 이상 붙어 있으면 그 선, 없으면 세로 안쪽 선)
    def inner_sep(j):
        for k in range(h, R0 - 1):
            if clean(trs[k]) and clean(trs[k + 1]):
                return hed.side(trs[k].findall(P('tc'))[j].get('borderFillIDRef'), 'bottom')
        cells = mid_ex.findall(P('tc'))
        for tc, s in ((cells[min(j, len(cells) - 1)], 'right'), (cells[min(j, len(cells) - 1)], 'left')):
            sp = hed.side(tc.get('borderFillIDRef'), s)
            if sp and sp[0] != 'NONE':
                return sp
        return ('SOLID', '0.12 mm', '#000000')

    # 칸 정렬: 숫자 칸 견본이 오른쪽 정렬이면 글자 칸은 가운데 정렬 문단 모양을 빌려 온다
    hdr = doc.header

    def align(pp):
        e = hdr.para.get(pp)
        a = e.find(H('align')) if e is not None else None
        return a.get('horizontal') if a is not None else 'JUSTIFY'
    pp_pool = collections.Counter()
    for tr in trs:
        for tc in tr.findall(P('tc')):
            for x in _tc_paras(tc):
                pp_pool[x.get('paraPrIDRef')] += 1
    center_pp = next((pp for pp, _ in pp_pool.most_common() if align(pp) == 'CENTER'), None)

    for tr in trs:
        tbl.remove(tr)
    zone = tbl.find(P('cellzoneList'))
    if zone is not None:
        tbl.remove(zone)
    total_h = 0
    new_trs = []
    for i, tr in enumerate(head_rows):
        tr = copy.deepcopy(tr)
        for j, tc in enumerate(tr.findall(P('tc'))):
            set_cell_text(tc, rows[i][j])
            sz = tc.find(P('cellSz'))
            if not use_ex and head_clean and sz is not None and j < len(widths):
                sz.set('width', str(widths[j]))
        total_h += max([tc_size(tc)[1] for tc in tr.findall(P('tc'))] + [0])
        new_trs.append(tr)
    all_rows = ([rows[0]] if not keep_head else []) + body_rows
    # 첫 줄이 사진 칸뿐이면(사진 표) 머리줄 모양(배경색·굵은 글자) 대신 본문 줄 모양을 쓴다
    photo_head = (not keep_head and any(PHOTO_RE.match(c or '') for c in rows[0])
                  and all(PHOTO_RE.match(c or '') or not c.strip() for c in rows[0]))
    nb = len(body_rows) + (1 if photo_head else 0)
    # 사진 표(사진 줄과 설명 줄이 번갈아 있는 양식)는 줄 종류에 맞는 견본 줄을 쓴다.
    # 견본을 하나만 쓰면 설명 줄이 사진 줄 높이로 커져 사진 아래가 크게 빈다
    kind_ex = None
    want_photo = [any(PHOTO_RE.match(c or '') for c in r) for r in all_rows]
    if ok and any(want_photo) and not all(want_photo):
        cand = [k for k in ok if k >= h] or ok

        def is_photo_tr(tr):
            return any(PHOTO_RE.match(tc_text(tc) or '') or photo_cell(tc) for tc in tr.findall(P('tc')))

        def tr_h(tr):
            return max([tc_size(tc)[1] for tc in tr.findall(P('tc'))] + [0])
        t_photo = [trs[k] for k in cand if is_photo_tr(trs[k])]
        t_text = [trs[k] for k in cand if not is_photo_tr(trs[k])]
        if not t_photo or not t_text:  # 양식에서 사진 줄을 못 알아보면 높이로 가른다(큰 줄=사진, 작은 줄=설명)
            by_h = sorted(cand, key=lambda k: tr_h(trs[k]))
            if tr_h(trs[by_h[0]]) * 2 <= tr_h(trs[by_h[-1]]):
                t_photo = [trs[by_h[-1]]]
                t_text = [trs[by_h[0]]]
            else:
                t_photo = t_text = []
        if t_photo and t_text:
            kind_ex = ({id(tr): True for tr in t_photo}, {id(tr): False for tr in t_text}, t_photo[0], t_text[0])
    for i, row in enumerate(all_rows):
        is_head = (not keep_head and i == 0 and not photo_head)
        bi = i - (0 if keep_head or photo_head else 1)
        r_index = (h + bi) if keep_head else i
        if is_head:
            ex_tr = head_ex
        else:
            ex_tr = last_ex if (bi == nb - 1 and nb >= 2) else mid_ex
            if kind_ex is not None:
                kinds = {**kind_ex[0], **kind_ex[1]}
                if kinds.get(id(ex_tr)) != want_photo[i]:
                    ex_tr = kind_ex[2] if want_photo[i] else kind_ex[3]
        cells = ex_tr.findall(P('tc'))
        tr = copy.deepcopy(ex_tr)
        for tc in tr.findall(P('tc')):
            tr.remove(tc)
        row_h = 0
        for j in range(C):
            src = cells[min(colmap(j), len(cells) - 1)]
            tc = copy.deepcopy(src)
            addr = tc.find(P('cellAddr'))
            if addr is not None:
                addr.set('colAddr', str(j))
                addr.set('rowAddr', str(r_index))
            sp = tc.find(P('cellSpan'))
            if sp is not None:
                sp.set('colSpan', '1')
                sp.set('rowSpan', '1')
            sz = tc.find(P('cellSz'))
            if sz is not None:
                sz.set('width', str(widths[j]))
                row_h = max(row_h, int(sz.get('height', '0') or 0))
            if not is_head and b_first is not None:
                jj = min(colmap(j), C0 - 1)
                first = head_ex if photo_head else b_first  # 사진 표의 첫 줄 위 선은 표 맨 위 선
                top = (hed.side(first.findall(P('tc'))[min(jj, len(first.findall(P('tc'))) - 1)].get('borderFillIDRef'), 'top')
                       if bi == 0 else inner_sep(jj))
                bottom = (hed.side(b_last.findall(P('tc'))[jj].get('borderFillIDRef'), 'bottom') if bi == nb - 1
                          else inner_sep(jj))
                tc.set('borderFillIDRef', hed.variant(tc.get('borderFillIDRef'), top=top, bottom=bottom))
            pp = None
            if not is_head and center_pp:
                # 오른쪽 정렬 칸의 글자, 왼쪽 정렬 칸의 짧은 숫자는 가운데 정렬로
                ps = _tc_paras(tc)
                al = align(ps[0].get('paraPrIDRef')) if ps else 'CENTER'
                num = is_numeric(row[j])
                if (al == 'RIGHT' and not num) or (al in ('LEFT', 'JUSTIFY') and num and len(row[j]) <= 14):
                    pp = center_pp
            set_cell_text(tc, row[j], para_pr=pp)
            tr.append(tc)
        total_h += row_h
        new_trs.append(tr)
    for tr in new_trs:
        tbl.append(tr)
    tbl.set('rowCnt', str(len(new_trs)))
    tbl.set('colCnt', str(C))
    sz = tbl.find(P('sz'))
    if sz is not None:
        sz.set('width', str(sum(widths)))
        sz.set('height', str(total_h))
    photo_frames(tbl, hed)
    ids.renew(p)
    strip_lineseg(p)
    return p, 'table%d' % tno


def replace_in(el, old, new):
    """el 안의 글자 old를 new로 바꾼다. 바꾼 횟수를 돌려준다.
    그대로는 없으면 띄어쓰기만 다른 글자를 찾는다(양식 '2025.  10.' ↔ 개요 '2025. 10.')."""
    cs = [c for c in old if not c.isspace()]
    if not cs:
        return 0
    pats = [re.compile(re.escape(old))]
    if len(cs) > 1:
        pats.append(re.compile(r'\s*'.join(map(re.escape, cs))))
    for pat in pats:
        n = 0
        for t in el.iter(P('t')):
            s = t_text(t)
            if pat.search(s):
                set_t(t, pat.sub(lambda m: new, s))
                n += 1
        if n:
            return n
        for p in el.iter(P('p')):
            s = para_text(p)
            if pat.search(s):
                segs, _ = t_segments(p)
                if segs:
                    lead = re.match(r'\s*', s).group(0)
                    fill_para(p, len(lead), len(lead), lead, '', pat.sub(lambda m: new, s[len(lead):]))
                    n += 1
        if n:
            return n
    return 0


def _years(s):
    return {int(y) for y in re.findall(r'(?<!\d)((?:19|20)\d\d)(?!\d)', s)}


def _set_big_text(p, s, hdr):
    segs, n = t_segments(p)
    if not segs:
        return
    best = max(segs, key=lambda sg: (hdr.pt(sg[0].get('charPrIDRef')) if t_text(sg[1]).strip() else 0))
    lead = re.match(r'\s*', para_text(p)).group(0)
    for sg in segs:
        set_t(sg[1], '')
    set_t(best[1], lead + s)
    for r in para_runs(p):
        if len(para_runs(p)) > 1 and not run_has_control(r) and all(not t_text(t) for t in run_ts(r)):
            p.remove(r)
    strip_lineseg(p)


def _ancestor(e, name):
    e = e.getparent() if e is not None else None
    while e is not None:
        if e.tag == P(name):
            return e
        e = e.getparent()
    return None


def _text_em(s):
    """글자 폭 어림(전각 글자 = 1)."""
    w = 0.0
    for ch in s:
        if ch == ' ':
            w += 0.35
        elif unicodedata.east_asian_width(ch) in 'WFA':
            w += 1.0
        else:
            w += 0.55
    return w


def _cell_need(tc, hdr):
    """칸 안 글자가 차지하는 높이 어림(HWPUNIT). 칸 너비에 따라 줄이 몇 번 꺾이는지 센다."""
    sz = tc.find(P('cellSz'))
    tbl = _ancestor(tc, 'tbl')
    m = tc.find(P('cellMargin')) if tc.get('hasMargin') == '1' else (tbl.find(P('inMargin')) if tbl is not None else None)
    try:
        inner = int(sz.get('width')) - (int(m.get('left')) + int(m.get('right')) if m is not None else 282)
    except Exception:
        return 0
    inner = max(inner, 1000)
    sub = tc.find(P('subList'))
    need = 0.0
    for p in (sub.findall(P('p')) if sub is not None else []):
        runs = [r for r in para_runs(p) if any(t_text(t).strip() for t in run_ts(r))] or para_runs(p)
        cp = max((r.get('charPrIDRef') for r in runs), key=hdr.pt, default=None)
        pt = hdr.pt(cp) if cp else 10.0
        scale = 1.0
        c = hdr.char.get(cp)
        if c is not None:
            sp, ra = c.find(H('spacing')), c.find(H('ratio'))
            try:
                scale = (1 + int(sp.get('hangul', 0)) / 100.0) * (int(ra.get('hangul', 100)) / 100.0)
            except Exception:
                pass
        ls = 1.6
        pp = hdr.para.get(p.get('paraPrIDRef'))
        e = pp.find('.//' + H('lineSpacing')) if pp is not None else None
        if e is not None and e.get('type', 'PERCENT') == 'PERCENT':
            try:
                ls = int(e.get('value')) / 100.0
            except Exception:
                pass
        n = sum(max(1, math.ceil(_text_em(seg) * scale * pt * 100 / inner)) for seg in para_text(p).split('\n'))
        need += n * pt * 100 * ls
    return need


def _grow_cell(tc, delta):
    """칸이 속한 줄(같은 행의 칸 모두)과 표의 높이를 delta 만큼 늘린다."""
    delta = int(math.ceil(delta))
    tbl = _ancestor(tc, 'tbl')
    addr = tc.find(P('cellAddr'))
    if delta <= 50 or tbl is None or addr is None:
        return
    row = addr.get('rowAddr')
    for tr in tbl.findall(P('tr')):
        for c in tr.findall(P('tc')):
            a = c.find(P('cellAddr'))
            sz = c.find(P('cellSz'))
            if a is not None and sz is not None and a.get('rowAddr') == row:
                sz.set('height', str(int(sz.get('height', '0')) + delta))
    tsz = tbl.find(P('sz'))
    if tsz is not None:
        tsz.set('height', str(int(tsz.get('height', '0')) + delta))


def set_title(blocks, title_info, title, hdr, base=0):
    """제목 자리(여러 줄 제목·표 칸 안 제목 포함)에 새 제목을 넣는다. 줄은 \n 으로 나눈다.
    제목이 길어져 표 칸 안에서 줄이 늘면 칸 높이도 늘린다(글자가 칸 밖으로 잘려 보이지 않게)."""
    lines = [x.strip() for x in title.replace('\\n', '\n').split('\n') if x.strip()] or ['']
    b = blocks[title_info['block'] - base]
    ps = list(b.iter(P('p')))
    group = [ps[k] for k in title_info['ps']] + [blocks[j - base] for j in title_info.get('next', [])]
    cells = []
    for p in group:
        tc = _ancestor(p, 'tc')
        if tc is not None and all(tc is not c for c in cells):
            cells.append(tc)
    before = [_cell_need(tc, hdr) for tc in cells]
    for i, p in enumerate(group):
        if i < len(lines):
            s = lines[i] if i < len(group) - 1 else '\n'.join(lines[i:])
            _set_big_text(p, s, hdr)
        else:
            par = p.getparent()
            if par is not None and len(par.findall(P('p'))) > 1:
                par.remove(p)
            else:
                _set_big_text(p, '', hdr)
    for tc, old in zip(cells, before):
        _grow_cell(tc, _cell_need(tc, hdr) - old)


def blank_png(w=210, h=297):
    raw = b''.join(b'\x00' + b'\xff' * (w * 3) for _ in range(h))

    def chunk(tag, data):
        return (struct.pack('>I', len(data)) + tag + data
                + struct.pack('>I', zlib.crc32(tag + data) & 0xffffffff))
    return (b'\x89PNG\r\n\x1a\n' + chunk(b'IHDR', struct.pack('>IIBBBBB', w, h, 8, 2, 0, 0, 0))
            + chunk(b'IDAT', zlib.compress(raw, 9)) + chunk(b'IEND', b''))


def drop_unused_bins(pkg):
    """새 문서에서 더는 쓰지 않는 그림 파일(빠진 표지의 로고 등)을 꾸러미에서도 지운다."""
    used = set()
    for n in pkg.names + list(pkg.changed):
        if n in pkg.removed or not n.endswith('.xml'):
            continue
        used.update(re.findall(rb'binaryItemIDRef="([^"]+)"', pkg.changed.get(n, pkg.data.get(n, b''))))
    try:
        hpf = pkg.xml('Contents/content.hpf')
    except Exception:
        return 0
    n = 0
    for it in list(hpf.iter('{%s}item' % NS_OPF)):
        href = it.get('href') or ''
        if href.startswith('BinData/') and it.get('id', '').encode() not in used:
            it.getparent().remove(it)
            pkg.removed.add(href)
            n += 1
    if n:
        pkg.put_xml('Contents/content.hpf', hpf)
    return n


def finish_package(pkg, sec_name, root, title):
    """미리보기(옛 내용이 남지 않게)·문서 정보·커서 위치를 새 내용에 맞춘다."""
    pkg.put_xml(sec_name, root)
    drop_unused_bins(pkg)
    lines = []
    for p in root.findall(P('p')):
        s = para_text(p).strip()
        if s:
            lines.append(s)
        tbl = first_table(p)
        if tbl is not None:
            for row in table_grid(tbl):
                lines.append(' | '.join(c.replace('\n', ' ') for c in row))
    prv = '\r\n'.join(lines)[:1024]
    if 'Preview/PrvText.txt' in pkg.data:
        pkg.changed['Preview/PrvText.txt'] = ('\r\n' + prv).encode('utf-8')
    if 'Preview/PrvImage.png' in pkg.data:
        pkg.changed['Preview/PrvImage.png'] = blank_png()
    try:
        hpf = pkg.xml('Contents/content.hpf')
        for t in hpf.iter('{%s}title' % NS_OPF):
            t.text = title or (lines[0] if lines else '')
        pkg.put_xml('Contents/content.hpf', hpf)
    except Exception:
        pass
    if 'settings.xml' in pkg.data:
        try:
            st = pkg.xml('settings.xml')
            for cp in st.iter('{%s}CaretPosition' % NS_HA):
                cp.set('listIDRef', '0')
                cp.set('paraIDRef', '0')
                cp.set('pos', '0')
            pkg.put_xml('settings.xml', st)
        except Exception:
            pass


def build(ref_path, outline, out_path, quiet=False):
    """양식(ref_path)의 디자인으로 개요(outline: 파일 경로 또는 글)를 새 문서(out_path)로 만든다."""
    if isinstance(outline, str) and os.path.isfile(outline):
        with open(outline, encoding='utf-8-sig') as f:
            outline = f.read()
    doc = RefDoc(ref_path)
    d, items = parse_outline(outline)
    warns = []
    try:
        rn, _, rs = gauge_pages(doc.pkg)
        ref_pages = rs or rn
        ref_cover = cover_pages(doc.pkg, doc.frame_end) if doc.cover else 0
    except Exception:
        ref_pages, ref_cover = None, 0
    ids = IdState(doc.root)
    frame_end = d['frame'] if d['frame'] is not None else doc.frame_end
    frame_end = max(1, min(frame_end, len(doc.blocks))) if doc.blocks else 0
    if any(b.kind in ('setup',) or 'secPr' in b.flags for b in doc.blocks[:1]) is False and frame_end == 0:
        frame_end = 1
    new_blocks = [copy.deepcopy(b.el) for b in doc.blocks[:frame_end]]
    if d['title']:
        if doc.title and doc.title['block'] + len(doc.title['next']) < frame_end:
            set_title(new_blocks, doc.title, d['title'], doc.header)
        else:
            warns.append('양식에서 제목 자리를 찾지 못해 @제목을 넣지 못했습니다. 본문 첫 줄로 쓰세요.')
    for old, new in d['replace']:
        n = sum(replace_in(b, old, new) for b in new_blocks)
        if not n:
            hint = ' / '.join('"%s"' % ' '.join(s.split())[:30] for s in doc.frame_texts[:6])
            warns.append('@바꾸기 "%s" → 틀 안에서 찾지 못했습니다.' % old
                         + (' 틀 안 글자 %s 중에서 그대로 복사해 다시 build 하세요.' % hint if hint else ''))
    # 표지·머리에 새 문서보다 앞선 연도가 남았는지(날짜 @바꾸기를 빠뜨리면 옛 날짜가 표지에 그대로 나간다)
    # 새 문서의 연도는 @제목·@바꾸기에 쓴 연도로 본다(본문의 "2026. 3. 1. 이후" 같은 앞날 날짜로 표지를 의심하지 않게).
    # 제목에 연도가 없을 때만 본문 연도를 쓴다.
    new_text = '\n'.join(l for l in outline.splitlines() if not re.match(r'\s*(//|@)', l))
    top = (max(_years((d['title'] or '') + ''.join(nw for _, nw in d['replace'])), default=None)
           or max(_years(new_text), default=None))
    if top:
        stale = []
        for b in new_blocks[:frame_end]:
            for p in b.iter(P('p')):
                s = para_text(p).strip()
                if s and s not in stale and any(y < top for y in _years(s)):
                    stale.append(s)
        if stale:
            warns.append('표지·머리에 옛 연도가 그대로 남아 있습니다: %s. 바꾸려면 @바꾸기: <그 글자 그대로> => 새 글자'
                         % ' / '.join('"%s"' % s[:30] for s in stale[:4]))
    st = {'prev': None, 'pending': False, 'blank': False, 'made': 0, 'moved': list(doc.moved_ctrls), 'first': None,
          'emitted': [], 'toc': []}
    counters = {}
    hints = align_outline(doc, items, frame_end)
    used = set()
    box_keys = {r.key for r in doc.box_roles}

    def emit(blk, key):
        if (st['prev'] is not None and not st['blank'] and not st['pending']
                and not (st['made'] == 0 and doc.body_new_page)):
            sp = doc.spacing(st['prev'], key)
            if (not sp and doc.blank_ex is not None and key in box_keys
                    and st['prev'].startswith('table') and not st['prev'].startswith('tablehead')):
                # 표 바로 뒤에 제목 상자가 오면 표 아래 선과 상자가 맞닿아 보인다 → 빈 줄 하나를 둔다
                sp = (doc.blank_ex,)
            for bi in sp:
                bl = copy.deepcopy(doc.blocks[bi].el)
                remove_ctrls(bl)
                strip_lineseg(bl)
                new_blocks.append(bl)
        if st['made'] == 0 and doc.body_new_page and frame_end == doc.frame_end:
            st['pending'] = True
        if st['pending']:
            blk.set('pageBreak', '1')
            st['pending'] = False
        if st['first'] is None:
            st['first'] = len(new_blocks)
        if st['moved'] and not has_inline_obj(blk):
            # 본문 중간에 있던 머리말·쪽 번호 설정을 새 본문 첫 글 문단 앞에 옮겨 단다.
            # 표·상자 문단 앞에 달면 한글이 그 설정 글자를 한 줄로 따로 잡아 빈 줄이 생긴다.
            attach_ctrls(blk, st['moved'])
            st['moved'] = []
        new_blocks.append(blk)
        st['emitted'].append((blk, key))
        st['prev'] = key
        st['blank'] = False
        st['made'] += 1

    for n_it, it in enumerate(items):
        kind = it[0]
        if kind == 'pagebreak':
            st['pending'] = True
            continue
        if kind == 'blank':
            if doc.blank_ex is not None:
                bl = copy.deepcopy(doc.blocks[doc.blank_ex].el)
                remove_ctrls(bl)
                strip_lineseg(bl)
                new_blocks.append(bl)
                st['blank'] = True
            continue
        if kind == 'toc':
            make_toc(doc, it[1], ids, warns, emit, st)
            continue
        if kind == 'orig':
            k = it[1]
            if not (0 <= k < len(doc.blocks)):
                warns.append('[원본 %d] 블록이 없습니다.' % k)
                continue
            blk = copy.deepcopy(doc.blocks[k].el)
            for old, new in d['replace']:
                replace_in(blk, old, new)
            ids.renew(blk)
            key = doc.block_key(doc.blocks[k])
        elif kind == 'table':
            tno = it[1] or doc.pick_table(it[2])
            if tno is None or tno not in doc.tables:
                if not doc.tables:
                    blk, key = make_plain_table(doc, it[2], ids, warns)
                else:
                    warns.append('[표 %s] 견본이 없어 기본 표 견본을 썼습니다.' % it[1])
                    blk, key = make_table_block(doc, doc.default_table, it[2], ids, warns)
            else:
                blk, key = make_table_block(doc, tno, it[2], ids, warns)
        else:
            blk, key = make_text_block(doc, it, ids, warns, counters, hints.get(n_it), used)
            if blk is not None and key in doc.heading_keys:
                # 윗단계 제목이 나오면 아랫단계 제목 번호는 1부터 다시
                for k2 in doc.heading_keys[doc.heading_keys.index(key) + 1:]:
                    counters.pop(k2, None)
                    counters.pop(k2 + '#n', None)
        if blk is None:
            continue
        emit(blk, key)
    if st['moved'] and st['first'] is not None:
        # 본문이 모두 표·상자뿐이면 첫 문단에 단다
        attach_ctrls(new_blocks[st['first']], st['moved'])
    made = st['made']
    if doc.photo_n:
        warns.append('사진 자리 %d개([사진1]~[사진%d])를 만들었습니다. 사용자에게 "개인정보 가리개의 [사진 넣기]에 이 파일과 사진을 '
                     '함께 끌어다 놓으면 차례로 들어갑니다"라고 알리세요.' % (doc.photo_n, doc.photo_n))
    if doc.frame_pics or doc.frame_orgs:
        pics, orgs = frame_marks(new_blocks[:frame_end] + [c for _, c in doc.moved_ctrls], doc.pkg)
        bits = (['그림 %d개(로고일 수 있음)' % pics] if pics else []) + \
               (['기관 이름 ' + ', '.join('"%s"' % o for o in orgs[:6])] if orgs else [])
        if bits:
            warns.append('틀에 그대로 남은 것: %s. 다른 기관 양식이면 사용자에게 확인하세요.' % ' · '.join(bits))
    split_photo_tables(new_blocks, frame_end, ids, warns, doc.hedit)
    keep_with_tables(new_blocks, frame_end, doc.hedit)
    try:
        heads = {k for k, r in doc.roles.items() if (r.cls in HEAD_CLASSES or r.cls in NUMBERED) and not r.labeled}
        keep_headings(new_blocks, st['emitted'], heads | box_keys, box_keys, doc.hedit)
    except Exception:
        pass  # 쪽 나눔 설정은 보기 좋게 하는 일이라, 못 해도 문서는 만든다
    root = doc.root
    for c in list(root):
        root.remove(c)
    for b in new_blocks:
        root.append(b)
    pkg = doc.pkg
    for extra in doc.sections[1:]:
        pkg.drop_section(extra)
    if len(doc.sections) > 1:
        warns.append('양식의 둘째 구역부터(%d개)는 새 문서에서 뺐습니다.' % (len(doc.sections) - 1))
    doc.hedit.save()
    finish_package(pkg, doc.sec_name, root, d['title'] or (doc.title['text'] if doc.title else ''))
    pkg.save(out_path)
    if st['toc']:
        try:
            warns += fill_toc_pages(out_path, pkg, doc.sec_name, root, st, set(doc.heading_keys))
        except Exception as e:
            warns.append('목차 쪽 번호를 자동으로 채우지 못했습니다(%s). 한글에서 쪽을 확인해 적어 주세요.' % e)
    rep = check(out_path, quiet=True)
    msg = ['[만들기 완료] %s' % out_path,
           '- 양식: %s · 틀 블록 %d개 유지 · 새 블록 %d개' % (os.path.basename(ref_path), frame_end, made)]
    try:
        opkg = Package(out_path)
        n, fill, _ = gauge_pages(opkg)
        cv = cover_pages(opkg, frame_end) if doc.cover and frame_end == doc.frame_end else 0
        body = n - cv if 0 < cv < n else 0
        line = '- 쪽 수: 약 %d쪽(어림, 한글과 1쪽쯤 다를 수 있음)' % n
        if body:
            line += ' = 표지 %d쪽 + 본문 약 %d쪽' % (cv, body)
        if ref_pages:
            line += ' · 양식 %d쪽' % ref_pages
            if 0 < ref_cover < ref_pages:
                line += '(본문 %d쪽)' % (ref_pages - ref_cover)
        label = '본문 ' if body else ''
        if d['pages']:
            lo, hi = d['pages']
            line += ' · 목표 %s%s' % (label, '%d쪽' % lo if lo == hi else '%d~%d쪽' % (lo, hi))
        msg.append(line)
        warns += pages_tips(body or n, fill, d['pages'], label)
    except Exception:
        pass
    seen = set()
    for w in warns:
        if w not in seen:
            msg.append('- 참고: ' + w)
            seen.add(w)
    msg.append(rep)
    out = '\n'.join(msg)
    if not quiet:
        print(out)
    return out


def fill_toc_para(p, entry, page):
    """목차 견본 문단에 '제목 ⇥ 쪽 번호'를 넣는다. 탭(점선 채움)과 쪽 번호 글자 모양은 견본 것을 쓴다."""
    segs, n = t_segments(p)
    full = ''.join(t_text(sg[1]) for sg in segs)
    k = full.rfind('\t')
    if not segs or k < 0:
        fill_para(p, 0, 0, '', '', entry + ('  ' + page if page else ''))
        return
    lead = re.match(r'\s*', full).group(0)
    ts = _anchor(segs, len(lead)) or segs[0]
    tb = _anchor(segs, k) or ts
    m = re.search(r'\d+\s*$', full)
    tp = (_anchor(segs, m.start()) if m and m.start() > k else None) or tb
    out = {id(sg[1]): '' for sg in segs}
    out[id(ts[1])] += lead + entry
    out[id(tb[1])] += '\t'
    out[id(tp[1])] += page
    for sg in segs:
        set_t(sg[1], out[id(sg[1])])
    for r in para_runs(p):
        if len(para_runs(p)) > 1 and not run_has_control(r) and all(not t_text(t) for t in run_ts(r)):
            p.remove(r)
    strip_lineseg(p)


def toc_auto(page):
    """목차 줄 쪽 번호를 엔진이 채울지: 비었거나 ?·자동."""
    return (page or '').strip() in ('', '?', '？', '자동', 'auto')


def _toc_key(s, strip_no=False):
    """목차 줄·제목 글자 비교용: 로마 숫자(Ⅰ→I)·빈칸·문장부호를 고르고, strip_no면 앞 번호(Ⅰ. 1. 1.1 가. 붙임)도 뗀다."""
    s = unicodedata.normalize('NFKC', s or '').strip()
    if strip_no:
        s = re.sub(r'^(붙\s*임|[IVXLC]+(?![a-z])|\d+(?:\s*\.\s*\d+)*|[가-하](?=\s*[.)]))\s*[.)]?\s*', '', s)
    return re.sub(r'[\s.,·:：()\[\]「」『』<>〈〉《》\-–—_]', '', s)


def _block_all_text(el):
    return ''.join(t_text(t) for t in el.iter(P('t')))


def rhwp_bin():
    """rhwp 실행 파일(있으면). 없으면 None — 쪽 번호는 엔진 어림으로 채운다. 환경 변수 RHWP=off면 쓰지 않는다(시험용)."""
    if os.environ.get('RHWP') == 'off':
        return None
    for c in (os.environ.get('RHWP'), shutil.which('rhwp'), os.path.expanduser('~/rhwp/target/release/rhwp')):
        if c and os.path.isfile(c) and os.access(c, os.X_OK):
            return c
    return None


def rhwp_pages(path):
    """rhwp 쪽 배치로 본 {첫 구역 문단 번호: 찍히는 쪽 번호}. rhwp가 없거나 실패하면 None."""
    b = rhwp_bin()
    if not b:
        return None
    try:
        r = subprocess.run([b, 'dump-pages', path, '--json'], capture_output=True, timeout=180)
        d = json.loads(r.stdout.decode('utf-8', 'replace'))
    except Exception:
        return None
    out = {}
    for pg in d.get('pages') or []:
        if pg.get('section', 0) != 0:
            continue
        for col in pg.get('columns') or []:
            for it in col.get('items') or []:
                pi = it.get('paraIndex')
                if isinstance(pi, int) and pi not in out:
                    out[pi] = pg.get('pageNumber') or (pg.get('pageIndex', 0) + 1)
    return out or None


def gauge_para_pages(pkg, root):
    """엔진 어림 쪽 배치로 본 {문단 번호: 찍히는 쪽 번호}. 쪽 번호 새로 시작(newNum)을 반영한다."""
    g = PageGauge(pkg.xml('Contents/header.xml'), [root])
    blocks = root.findall(P('p'))
    where = []
    g.pages(blocks, where)
    starts = []
    for i, p in enumerate(blocks):
        for nn in p.iter(P('newNum')):
            if nn.get('numType') == 'PAGE':
                try:
                    starts.append((where[i], int(nn.get('num'))))
                except (TypeError, ValueError):
                    pass
    out = {}
    for i, pg in enumerate(where):
        base = [(s, n) for s, n in starts if s <= pg]
        out[i] = base[-1][1] + pg - base[-1][0] if base else pg
    return out


def fill_toc_pages(out_path, pkg, sec_name, root, st, heads):
    """다 만든 문서에서 목차 줄마다 같은 제목을 찾아 쪽 번호를 채우고 다시 저장한다. 참고 글 목록을 돌려준다.
    쪽 번호가 비었거나 ?·자동인 줄만 채우고, 적힌 번호는 그대로 둔다(실제와 다르면 알린다)."""
    blocks = root.findall(P('p'))
    idx = {id(b): i for i, b in enumerate(blocks)}
    pages, how = rhwp_pages(out_path), 'rhwp'
    if pages is None:
        pages, how = gauge_para_pages(pkg, root), 'gauge'
    hdr = Header(pkg.xml('Contents/header.xml'))
    keep = {k for k, pp in hdr.para.items() if any(b.get('keepWithNext') == '1' for b in pp.iter(H('breakSetting')))}

    def page_of(i):
        # rhwp·어림은 '다음 문단과 함께'를 따르지 않는다. 한글은 묶인 제목을 뒤 블록(표 등)과 같은 쪽으로 넘기므로 그 쪽을 쓴다
        j = i
        while j + 1 < len(blocks) and blocks[j].get('paraPrIDRef') in keep and blocks[j + 1].get('pageBreak') != '1':
            j += 1
        a, b = pages.get(i), pages.get(j)
        return min(b, a + 1) if a is not None and b is not None and b > a else a
    toc_end = max((idx.get(id(b), -1) for b, _, _ in st['toc']), default=-1)
    cands = sorted((idx[id(el)], key, _block_all_text(el)) for el, key in st['emitted']
                   if id(el) in idx and idx[id(el)] > toc_end and not key.startswith('toc'))
    hc = [c for c in cands if c[1] in heads]

    def find(entry, cur):
        for pool in (hc, cands):
            for strip in (False, True):
                k = _toc_key(entry, strip)
                if not k:
                    continue
                for i, _, txt in pool:
                    if i > cur and _toc_key(txt, strip) == k:
                        return i
        return None
    cur, filled, missing, differ = toc_end, 0, [], []
    for blk, entry, page in st['toc']:
        hit = find(entry, cur)
        if hit is None:
            if not page:
                missing.append(entry)
            continue
        cur = hit
        pg = page_of(hit)
        if pg is None:
            continue
        if not page:
            fill_toc_para(blk, entry, str(pg))
            filled += 1
        elif page.strip() != str(pg):
            differ.append('"%s" %s → %d' % (entry.strip()[:20], page.strip(), pg))
    if filled:
        pkg.put_xml(sec_name, root)
        pkg.save(out_path)
    tips = []
    if filled:
        tips.append('목차 쪽 번호 %d줄을 %s 채웠습니다(쪽 끝 제목이 다음 쪽 내용과 함께 넘어가는 것까지 셈). '
                    '한글과 1쪽쯤 다를 수 있으니 한글에서 확인하세요.'
                    % (filled, '실제 쪽 배치(rhwp)로' if how == 'rhwp' else '어림 쪽 배치로'))
    if missing:
        tips.append('목차 %d줄은 본문에서 같은 제목을 찾지 못해 쪽 번호를 비워 두었습니다: %s. 목차 줄 글자를 본문 제목과 똑같이 쓰세요.'
                    % (len(missing), ' / '.join('"%s"' % m.strip()[:20] for m in missing[:4])))
    if differ:
        tips.append('목차에 적힌 쪽 번호가 %s 센 쪽과 다른 줄이 있습니다: %s. 적힌 번호는 그대로 두었으니 한글에서 확인하세요'
                    '(쪽 번호 칸을 비워 두면 자동으로 채웁니다).' % ('rhwp로' if how == 'rhwp' else '어림으로', ' / '.join(differ[:4])))
    if not tips:
        tips.append('목차 쪽 번호는 개요에 적힌 대로 넣었습니다. 한글에서 실제 쪽과 맞는지 확인하세요.')
    return tips


def make_toc(doc, entries, ids, warns, emit, st):
    """[목차] … [/목차] → 양식의 목차 제목·단계별 목차 줄 견본으로 목차를 만든다."""
    if not entries:
        warns.append('[목차] 안에 줄이 없어 목차를 만들지 않았습니다. [목차] 다음 줄부터 "제목 | 쪽 번호"를 쓰고 [/목차]로 닫으세요.')
        return
    if not doc.toc_samples:
        warns.append('양식에 목차 견본이 없어 목차 줄을 본문 글자로 만들었습니다.')
        for e in entries:
            if e[0] == 'pagebreak':
                st['pending'] = True
                continue
            entry, page = e
            role = doc.roles.get('plain') or max(doc.roles.values(), key=lambda r: len(r.blocks))
            blk = copy.deepcopy(doc.blocks[role.ex].el)
            remove_ctrls(blk)
            for a in ('pageBreak', 'columnBreak'):
                if blk.get(a) is not None:
                    blk.set(a, '0')
            auto = toc_auto(page)
            fill_para(blk, role.a, role.b, role.lead, '', entry + ('  ' + page if page and not auto else ''), role.body_cp)
            ids.renew(blk)
            emit(blk, role.key)
            st['toc'].append((blk, role.lead + entry, '' if auto else page))
        return
    if doc.toc_head is not None:
        blk = copy.deepcopy(doc.blocks[doc.toc_head].el)
        remove_ctrls(blk)
        blk.set('pageBreak', '0')
        ids.renew(blk)
        strip_lineseg(blk)
        emit(blk, 'tochead')
    for e in entries:
        if e[0] == 'pagebreak':
            st['pending'] = True
            continue
        entry, page = e
        sig = toc_sig(entry)
        bi = doc.toc_samples.get(sig)
        if bi is None:
            for alt in TOC_FALLBACK.get(sig, []) + list(doc.toc_samples):
                if alt in doc.toc_samples:
                    bi = doc.toc_samples[alt]
                    break
        blk = copy.deepcopy(doc.blocks[bi].el)
        remove_ctrls(blk)
        for a in ('pageBreak', 'columnBreak'):
            if blk.get(a) is not None:
                blk.set(a, '0')
        auto = toc_auto(page)
        fill_toc_para(blk, entry, '' if auto else page)
        ids.renew(blk)
        emit(blk, 'toc:' + sig)
        st['toc'].append((blk, entry, '' if auto else page))  # 쪽 번호는 다 만든 뒤 fill_toc_pages가 채운다


def make_plain_table(doc, rows, ids, warns):
    """양식에 표가 하나도 없을 때: 테두리 정의를 header에 덧붙여 단순한 표를 만든다(기존 서식은 그대로)."""
    bf_body = doc.hedit.simple(None)
    bf_head = doc.hedit.simple('#E7E6E6')
    role = doc.roles.get('plain') or (max(doc.roles.values(), key=lambda r: len(r.blocks)) if doc.roles else None)
    src = doc.blocks[role.ex].el if role else doc.blocks[min(len(doc.blocks) - 1, doc.frame_end)].el
    p = copy.deepcopy(src)
    remove_ctrls(p, keep_objects=False)
    for r in para_runs(p)[1:]:
        p.remove(r)
    run = para_runs(p)[0] if para_runs(p) else etree.SubElement(p, P('run'))
    for c in list(run):
        run.remove(c)
    cp = role.body_cp if role else run.get('charPrIDRef', '0')
    rows = [r for r in rows if any(c.strip() for c in r)] or [['']]
    numbered = []
    for r in rows:
        r, doc.photo_n = number_photos(r, doc.photo_n)
        numbered.append(r)
    rows = numbered
    # 첫 줄이 사진 자리뿐이면 머리줄(회색 배경)로 만들지 않는다
    photo_head = (any(PHOTO_RE.match(c or '') for c in rows[0])
                  and all(PHOTO_RE.match(c or '') or not c.strip() for c in rows[0]))
    C_ = max(len(r) for r in rows)
    rows = [r + [''] * (C_ - len(r)) for r in rows]
    W = 46000
    widths = _col_widths(rows, C_, W, None)
    tbl = etree.SubElement(run, P('tbl'))
    for k, v in (('id', ids.new()), ('zOrder', '0'), ('numberingType', 'TABLE'), ('textWrap', 'TOP_AND_BOTTOM'),
                 ('textFlow', 'BOTH_SIDES'), ('lock', '0'), ('dropcapstyle', 'None'), ('pageBreak', 'CELL'),
                 ('repeatHeader', '1'), ('rowCnt', str(len(rows))), ('colCnt', str(C_)), ('cellSpacing', '0'),
                 ('borderFillIDRef', bf_body), ('noAdjust', '0')):
        tbl.set(k, v)
    ids.z += 1
    tbl.set('zOrder', str(ids.z))
    rh = 1800
    sz = etree.SubElement(tbl, P('sz'))
    for k, v in (('width', str(sum(widths))), ('widthRelTo', 'ABSOLUTE'), ('height', str(rh * len(rows))),
                 ('heightRelTo', 'ABSOLUTE'), ('protect', '0')):
        sz.set(k, v)
    pos = etree.SubElement(tbl, P('pos'))
    for k, v in (('treatAsChar', '1'), ('affectLSpacing', '0'), ('flowWithText', '1'), ('allowOverlap', '0'),
                 ('holdAnchorAndSO', '0'), ('vertRelTo', 'PARA'), ('horzRelTo', 'PARA'), ('vertAlign', 'TOP'),
                 ('horzAlign', 'LEFT'), ('vertOffset', '0'), ('horzOffset', '0')):
        pos.set(k, v)
    for tag, vals in (('outMargin', ('283', '283', '283', '283')), ('inMargin', ('510', '510', '141', '141'))):
        e = etree.SubElement(tbl, P(tag))
        for k, v in zip(('left', 'right', 'top', 'bottom'), vals):
            e.set(k, v)
    for i, row in enumerate(rows):
        tr = etree.SubElement(tbl, P('tr'))
        for j, txt in enumerate(row):
            tc = etree.SubElement(tr, P('tc'))
            head = i == 0 and not photo_head
            for k, v in (('name', ''), ('header', '1' if head else '0'), ('hasMargin', '0'), ('protect', '0'),
                         ('editable', '0'), ('dirty', '0'), ('borderFillIDRef', bf_head if head else bf_body)):
                tc.set(k, v)
            sub = etree.SubElement(tc, P('subList'))
            for k, v in (('id', ''), ('textDirection', 'HORIZONTAL'), ('lineWrap', 'BREAK'), ('vertAlign', 'CENTER'),
                         ('linkListIDRef', '0'), ('linkListNextIDRef', '0'), ('textWidth', '0'), ('textHeight', '0'),
                         ('hasTextRef', '0'), ('hasNumRef', '0')):
                sub.set(k, v)
            for ln in (txt.split('\n') if txt else ['']):
                cp_ = etree.SubElement(sub, P('p'))
                for k, v in (('id', '0'), ('paraPrIDRef', p.get('paraPrIDRef', '0')), ('styleIDRef', '0'),
                             ('pageBreak', '0'), ('columnBreak', '0'), ('merged', '0')):
                    cp_.set(k, v)
                cr = etree.SubElement(cp_, P('run'))
                cr.set('charPrIDRef', cp)
                ct = etree.SubElement(cr, P('t'))
                ct.text = ln
            e = etree.SubElement(tc, P('cellAddr'))
            e.set('colAddr', str(j))
            e.set('rowAddr', str(i))
            e = etree.SubElement(tc, P('cellSpan'))
            e.set('colSpan', '1')
            e.set('rowSpan', '1')
            e = etree.SubElement(tc, P('cellSz'))
            e.set('width', str(widths[j]))
            e.set('height', str(rh))
            e = etree.SubElement(tc, P('cellMargin'))
            for k, v in zip(('left', 'right', 'top', 'bottom'), ('510', '510', '141', '141')):
                e.set(k, v)
    if photo_head:
        tbl.set('repeatHeader', '0')
    photo_frames(tbl, doc.hedit)
    etree.SubElement(run, P('t'))
    strip_lineseg(p)
    warns.append('양식에 표가 없어 기본 모양(검은 실선·회색 머리줄)의 표를 만들었습니다.')
    return p, 'table-new'


# ---------------------------------------------------------------- 점검

PERSONAL_PATTERNS = [
    ('주민등록번호', re.compile(r'(?<!\d)\d{6}\s*-\s*[1-4]\d{6}(?!\d)')),
    ('휴대전화 번호', re.compile(r'(?<!\d)01[016789][-\s.]?\d{3,4}[-\s.]?\d{4}(?!\d)')),
    ('전자우편 주소', re.compile(r'[\w.+-]+@[\w-]+\.[\w.]+')),
]


# ---------------------------------------------------------------- 쪽 수 어림

GAUGE_OBJ = {'tbl', 'pic', 'container', 'rect', 'ellipse', 'arc', 'polygon', 'curve', 'line',
             'connectLine', 'textart', 'ole', 'equation', 'chart', 'video'}


NARROW_W = dict([(c, 0.33) for c in '.,:;\'"()[]{}!|`-'] + [(c, 0.5) for c in '0123456789'] + [('/', 0.4), ('%', 0.8)])


def _char_w(ch):
    """글자 폭(글자 크기 대비): 한글·한자·전각 기호 1, 빈칸 0.5(한글 뷰어로 잼), 숫자 0.5, 문장부호 0.33, 그 밖 반각 0.55."""
    if ch in ' \u00a0':
        return 0.5
    if ch == '\t':
        return 2.0
    w = NARROW_W.get(ch)
    if w:
        return w
    o = ord(ch)
    if o < 0x2000 or 0xff61 <= o <= 0xffdc:
        return 0.55
    return 1.0


class PageGauge:
    """한글이 쪽을 나누는 방식을 흉내 내 쪽 수를 어림한다(한글과 1쪽쯤 다를 수 있음).
    한글이 저장한 줄 배치(linesegarray)가 남은 문단은 그 높이를, 없는 문단은 글자 폭·글자 크기·줄 간격으로 잰 높이를 쓴다.
    글꼴마다 글자 폭이 달라서, 양식에 남은 줄 배치로 폭 비율(k)을 한 번 맞춘다."""

    def __init__(self, hdr_root, roots):
        self.hdr = Header(hdr_root)
        self._c, self._p = {}, {}
        self.k = 1.0
        self.k = self._calibrate(roots)

    def ch(self, cid):
        if cid not in self._c:
            c = self.hdr.char.get(cid)
            v = [1000, 100, 100, 0, 0]  # 글자 크기, 장평(한글·영문), 자간(한글·영문)
            if c is not None:
                try:
                    v[0] = int(c.get('height') or 1000)
                    r, sp = c.find(H('ratio')), c.find(H('spacing'))
                    if r is not None:
                        v[1], v[2] = int(r.get('hangul', 100)), int(r.get('latin', 100))
                    if sp is not None:
                        v[3], v[4] = int(sp.get('hangul', 0)), int(sp.get('latin', 0))
                except (TypeError, ValueError):
                    pass
            self._c[cid] = tuple(v)
        return self._c[cid]

    def width(self, x, cid):
        fs, rh, rl, sh, sl = self.ch(cid)
        w = _char_w(x)
        return fs * ((w * rh + sh) if w >= 1 else (w * rl + sl)) / 100.0

    def pp(self, pid):
        if pid not in self._p:
            d = {'left': 0, 'right': 0, 'intent': 0, 'prev': 0, 'next': 0, 'lt': 'PERCENT', 'lv': 160}
            pp = self.hdr.para.get(pid)
            if pp is not None:
                m = pp.find('.//' + H('margin'))  # 첫 번째(hp:case) 값
                for k in ('intent', 'left', 'right', 'prev', 'next'):
                    e = m.find(C(k)) if m is not None else None
                    try:
                        d[k] = int(e.get('value'))
                    except (AttributeError, TypeError, ValueError):
                        pass
                ls = pp.find('.//' + H('lineSpacing'))
                if ls is not None:
                    d['lt'] = ls.get('type', 'PERCENT')
                    try:
                        d['lv'] = int(ls.get('value'))
                    except (TypeError, ValueError):
                        pass
            self._p[pid] = d
        return self._p[pid]

    @staticmethod
    def pitch(fs, d):
        t, v = d['lt'], d['lv']
        if t == 'FIXED':
            return max(v, 1)
        if t == 'BETWEEN_LINES':
            return fs + v
        if t == 'AT_LEAST':
            return max(fs, v)
        return fs * v / 100.0

    def _calibrate(self, roots):
        """양식의 꽉 찬 줄(문단의 마지막 줄 말고)에서 '줄 폭 ÷ 어림 글자 폭'의 가운데 값."""
        ks = []
        for root in roots:
            for p in root.iter(P('p')):
                la = p.find(P('linesegarray'))
                if la is None or len(la) < 2 or any(c.tag != P('t') or len(c) for r in para_runs(p) for c in r):
                    continue
                chars = [(x, r.get('charPrIDRef')) for r in para_runs(p) for t in run_ts(r) for x in (t.text or '')]
                segs = la.findall(P('lineseg'))
                for a, b in zip(segs, segs[1:]):
                    try:
                        part = chars[int(a.get('textpos')):int(b.get('textpos'))]
                        hz = int(a.get('horzsize'))
                    except (TypeError, ValueError):
                        continue
                    w = sum(self.width(x, cid) for x, cid in part)
                    if len(part) >= 8 and w > 0:
                        ks.append(hz / w)
        return max(0.8, min(1.3, statistics.median(ks))) if len(ks) >= 3 else 1.0

    def objects(self, p):
        """(글자처럼 취급한 개체 [(개체, 높이)], 글 위아래를 밀어내는 떠 있는 개체 높이 합)."""
        inline, floating = [], 0
        for r in para_runs(p):
            for c in r:
                if local(c.tag) not in GAUGE_OBJ:
                    continue
                pos, sz, om = c.find(P('pos')), c.find(P('sz')), c.find(P('outMargin'))
                try:
                    hh = int(sz.get('height')) if sz is not None else 0
                    if om is not None:
                        hh += int(om.get('top', 0) or 0) + int(om.get('bottom', 0) or 0)
                except (TypeError, ValueError):
                    hh = 0
                if pos is not None and pos.get('treatAsChar') == '1':
                    inline.append((c, hh))
                elif c.get('textWrap') == 'TOP_AND_BOTTOM':
                    floating += hh
        return inline, floating

    def para(self, p, avail):
        """문단 높이, 쪽 끝에서 넘쳐도 되는 아래 여백(마지막 줄 간격 + 문단 아래), 통째로만 넘어가는지."""
        d = self.pp(p.get('paraPrIDRef'))
        gap = max(d['prev'], 0) + max(d['next'], 0)
        inline, floating = self.objects(p)
        la = p.find(P('linesegarray'))
        if la is not None and len(la):
            h = sp = 0
            for ls in la.findall(P('lineseg')):
                try:
                    sp = int(ls.get('spacing'))
                    h += int(ls.get('vertsize')) + sp
                except (TypeError, ValueError):
                    pass
            return gap + h + floating, max(d['next'], 0) + max(sp, 0), bool(inline)
        ws, fs, first = [0.0], 0, None
        for r in para_runs(p):
            cid = r.get('charPrIDRef')
            s = ''.join(t_text(t) for t in run_ts(r))
            if first is None:
                first = self.ch(cid)[0]
            if s.strip():
                fs = max(fs, self.ch(cid)[0])
            for x in s:
                if x == '\n':
                    ws.append(0.0)
                else:
                    ws[-1] += self.width(x, cid)
        fs = fs or first or 1000
        pit = self.pitch(fs, d)
        base = avail - d['left'] - d['right']
        c1 = max(base - max(d['intent'], 0), avail * 0.2)
        c2 = max(base - max(-d['intent'], 0), avail * 0.2)
        lines = sum(1 if w * self.k <= c1 else 1 + math.ceil((w * self.k - c1) / c2) for w in ws)
        h = lines * pit
        if inline:
            oh = max(max(hh, self.table(c)) if local(c.tag) == 'tbl' else hh for c, hh in inline)
            h += max(0, oh - fs)
        return gap + h + floating, max(d['next'], 0) + max(0, pit - fs), bool(inline)

    def table(self, tbl):
        im = tbl.find(P('inMargin'))
        dm = [int(im.get(k, 0) or 0) for k in ('left', 'right', 'top', 'bottom')] if im is not None else [141] * 4
        om = tbl.find(P('outMargin'))
        total = int(om.get('top', 0) or 0) + int(om.get('bottom', 0) or 0) if om is not None else 0
        for tr in tbl.findall(P('tr')):
            rh = 0
            for tc in tr.findall(P('tc')):
                if tc_span(tc)[1] > 1:
                    continue
                w, hgt = tc_size(tc)
                mg = dm
                cm = tc.find(P('cellMargin'))
                if tc.get('hasMargin') == '1' and cm is not None:
                    mg = [int(cm.get(k, 0) or 0) for k in ('left', 'right', 'top', 'bottom')]
                sub = tc.find(P('subList'))
                inner = tail = 0
                for q in (sub.findall(P('p')) if sub is not None else []):
                    h, tail, _ = self.para(q, max(w - mg[0] - mg[1], 1000))
                    inner += h
                rh = max(rh, hgt, inner - tail + mg[2] + mg[3])  # 칸 안 마지막 줄 간격은 칸 높이에 들지 않는다
            total += rh
        return total

    def pages(self, blocks, where=None):
        """(쪽 수, 마지막 쪽을 채운 비율). where(목록)를 주면 문단마다 시작하는 쪽(1부터)을 차례로 담는다."""
        W, Hh = 48190, 70018  # A4 기본 여백
        for b in blocks:
            pp = next(b.iter(P('pagePr')), None)
            if pp is None:
                continue
            try:
                land = pp.get('landscape') == 'NARROWLY'
                W, Hh = int(pp.get('height' if land else 'width')), int(pp.get('width' if land else 'height'))
                m = pp.find(P('margin'))
                if m is not None:
                    W -= sum(int(m.get(k, '0') or 0) for k in ('left', 'right', 'gutter'))
                    Hh -= sum(int(m.get(k, '0') or 0) for k in ('top', 'bottom', 'header', 'footer'))
            except (TypeError, ValueError):
                pass
            break
        y, n = 0.0, 1
        for p in blocks:
            if p.get('pageBreak') == '1' and y > 0:
                n, y = n + 1, 0.0
            h, tail, solid = self.para(p, W)
            start = n
            if y + h - tail <= Hh:
                y += h
            elif solid:  # 글자처럼 취급한 표·그림은 쪽을 넘겨 나뉘지 않고 통째로 다음 쪽으로 간다
                if y > 0:
                    n += 1
                start = n
                y = min(h, Hh)
            else:
                if Hh - y < min(h, 1500):  # 첫 줄도 들어가지 않으면 다음 쪽에서 시작
                    start = n + 1
                y += h
                while y > Hh:
                    n, y = n + 1, y - Hh
            if where is not None:
                where.append(start)
        return n, y / Hh if Hh else 0


def saved_pages(roots):
    """한글이 저장한 줄 배치로 센 쪽 수(줄 세로 위치가 되돌아가는 곳이 새 쪽). 줄 배치가 빠진 문단이 있으면 None."""
    n = 0
    for root in roots:
        n += 1
        prev = None
        for p in root.findall(P('p')):
            la = p.find(P('linesegarray'))
            if la is None or not len(la):
                return None
            for ls in la.findall(P('lineseg')):
                try:
                    v = int(ls.get('vertpos'))
                except (TypeError, ValueError):
                    return None
                if prev is not None and v < prev:
                    n += 1
                prev = v
    return n


def gauge_pages(pkg):
    """(어림 쪽 수, 마지막 쪽 채운 비율, 한글이 저장한 쪽 수 또는 None). 구역마다 새 쪽에서 시작한다."""
    roots = [pkg.xml(sn) for sn in pkg.section_names()]
    g = PageGauge(pkg.xml('Contents/header.xml'), roots)
    n, fill = 0, 0.0
    for root in roots:
        k, fill = g.pages(root.findall(P('p')))
        n += k
    return n, fill, saved_pages(roots)


def cover_pages(pkg, cover_end):
    """표지(첫 구역의 블록 0~cover_end-1)가 차지하는 쪽 수(어림). 본문이 새 쪽에서 시작하지 않으면 0.
    표지와 본문 사이의 빈 문단은 표지 쪽에 든다."""
    if not cover_end:
        return 0
    roots = [pkg.xml(sn) for sn in pkg.section_names()]
    blocks = roots[0].findall(P('p'))
    k = cover_end
    while (k < len(blocks) and blocks[k].get('pageBreak') != '1' and not para_text(blocks[k]).strip()
           and not any(local(c.tag) in GAUGE_OBJ for r in para_runs(blocks[k]) for c in r)):
        k += 1
    if k >= len(blocks) or blocks[k].get('pageBreak') != '1':
        return 0
    g = PageGauge(pkg.xml('Contents/header.xml'), roots)
    return g.pages(blocks[:k])[0]


def pages_tips(n, fill, target=None, label=''):
    """어림 쪽 수로 줄 참고 글. target=(최소, 최대) 쪽. label은 표지를 뺀 쪽 수일 때 '본문 '."""
    tips = []
    again = '(다시 만들기는 두 번까지. 그래도 맞지 않으면 그대로 전달하며 어림 쪽 수를 알린다)'
    if target:
        lo, hi = target
        goal = label + ('%d쪽' % lo if lo == hi else '%d~%d쪽' % (lo, hi))
        if n == hi + 1 and fill <= 0.12:
            tips.append('어림 %s%d쪽(마지막 쪽은 몇 줄)으로 목표 %s보다 조금 깁니다. 덜 중요한 ◦·※ 줄 몇 개만 줄여 다시 build 하세요%s.'
                        % (label, n, goal, again))
        elif n > hi or (n == hi and fill >= 0.93):
            tips.append('어림 %s%d쪽으로 목표 %s보다 길 수 있습니다. 덜 중요한 ◦·※ 줄과 겹치는 말을 줄이거나 표 줄을 합쳐 다시 build 하세요%s.'
                        % (label, n, goal, again))
        elif n < lo:
            tips.append('어림 %s%d쪽으로 목표 %s보다 짧습니다. 소제목을 나누고 ◦ 아래에 - 근거(수치·일정·대상·방법)를 2~3개씩 더하거나 '
                        '※ 참고를 더해 다시 build 하세요(같은 말 되풀이 금지, 모르는 사실은 ○○)%s.' % (label, n, goal, again))
    elif n > 1 and fill >= 0.93:
        tips.append('마지막 쪽이 거의 꽉 찼습니다(어림). 한글에서 한 쪽 더 넘어갈 수 있습니다.')
    elif n > 1 and fill <= 0.12:
        tips.append('마지막 쪽에 몇 줄만 넘어간 것으로 보입니다(어림). 한 쪽 줄이려면 조금만 줄이면 됩니다.')
    return tips


PLACEHOLDER_RE = re.compile(
    r'(?:헤드라인M|HY헤드라인M?|휴먼명조|휴면명조|신명조|견명조|HY중고딕|중고딕|맑은\s?고딕|함초롬(?:바탕|돋움))'
    r'\s*(?:체|폰트|글꼴)?\s*[,(]?\s*\d{1,2}(?:\.\d)?\s*(?:pt|포인트)'
    r'|보고서\s*양식|\(\s*제\s*목\s*\)|(?:제목|내용|본문)을?\s*입력|여기에\s*(?:입력|작성)|입력하(?:세요|십시오)')


def scan_personal(text):
    found = []
    for name, rx in PERSONAL_PATTERNS:
        if rx.search(text):
            found.append(name)
    return found


MASK_RE = re.compile(r'[\[［【]\s*(이름|학번|주민번호|전화|메일|계좌|주소|생일|기타)\s*\d+\s*[\]］】]')


def lint_text(text):
    tips = []
    masks = MASK_RE.findall(text)
    if masks:
        tips.append('가림 표시 %d곳([이름1] 같은 것)이 있습니다. 그대로 두세요 — \'개인정보 가리개\'의 '
                    '되돌리기에서 원래 값으로 바뀝니다.' % len(masks))
    if re.search(r'○○|ＯＯ|OOO|XXX|\{\{|\}\}|△△', text):
        tips.append('채우지 않은 자리(○○, {{ }} 등)가 남아 있습니다.')
    ph = sorted({m.group(0) for m in PLACEHOLDER_RE.finditer(text)})
    if ph:
        tips.append('양식의 안내 글자(자리표시)로 보이는 글자가 남아 있습니다: %s. 새 문서에 맞게 지우거나 바꾸세요.'
                    % ', '.join('"%s"' % x for x in ph[:5]))
    if re.search(r'\*\*|^#{1,6}\s|`', text, re.M):
        tips.append('** 나 # 같은 마크다운 기호가 남아 있습니다.')
    m = re.search(r'(?<![\d.])(20\d\d)[./-](\d{1,2})[./-](\d{1,2})(?![\d])', text)
    if m:
        tips.append('날짜 "%s"는 공문서 표기("%s. %d. %d.")로 바꾸는 것이 좋습니다.' % (
            m.group(0), m.group(1), int(m.group(2)), int(m.group(3))))
    m = re.search(r'(?<![\d])(\d{1,2})시\s*(\d{1,2})분', text)
    if m:
        tips.append('시간 "%s"는 "%02d:%02d"처럼 쓰는 것이 공문서 표기입니다.' % (m.group(0), int(m.group(1)), int(m.group(2))))
    return tips


def check(path, quiet=False):
    """파일 구조(열릴지)·표 구조·참조 번호·공문 표기·개인정보를 점검한다."""
    errs = []
    tips = []
    try:
        pkg = Package(path)
    except HwpError as e:
        out = '[점검] 열 수 없음: %s' % e
        if not quiet:
            print(out)
        return out
    if not pkg.names or pkg.names[0] != 'mimetype':
        errs.append('mimetype 항목이 맨 앞에 있지 않습니다.')
    elif pkg.zf.getinfo('mimetype').compress_type != zipfile.ZIP_STORED:
        errs.append('mimetype 항목이 압축되어 있습니다.')
    if pkg.data.get('mimetype', b'').strip() != b'application/hwp+zip':
        errs.append('mimetype 값이 한글 문서가 아닙니다.')
    roots = {}
    for n in pkg.names:
        if n.endswith(('.xml', '.hpf', '.rdf')):
            try:
                roots[n] = pkg.xml(n)
            except Exception as e:
                errs.append('%s XML 오류: %s' % (n, str(e)[:80]))
    hpf = roots.get('Contents/content.hpf')
    if hpf is not None:
        for it in hpf.iter('{%s}item' % NS_OPF):
            href = it.get('href')
            if href and href not in pkg.data:
                errs.append('목록에 있는 %s 파일이 없습니다.' % href)
    hdr = roots.get('Contents/header.xml')
    ids = {'charPrIDRef': set(), 'paraPrIDRef': set(), 'borderFillIDRef': set(), 'styleIDRef': set()}
    if hdr is not None:
        ids['charPrIDRef'] = {e.get('id') for e in hdr.iter(H('charPr'))}
        ids['paraPrIDRef'] = {e.get('id') for e in hdr.iter(H('paraPr'))}
        ids['borderFillIDRef'] = {e.get('id') for e in hdr.iter(H('borderFill'))}
        ids['styleIDRef'] = {e.get('id') for e in hdr.iter(H('style'))}
    text_all = []
    npara = 0
    ntbl = 0
    for sn in pkg.section_names():
        sec = roots.get(sn)
        if sec is None:
            continue
        bad = collections.Counter()
        for e in sec.iter():
            for a, pool in ids.items():
                v = e.get(a)
                if v is not None and pool and v not in pool:
                    bad[a] += 1
        for a, c in bad.items():
            errs.append('%s: 없는 서식 번호를 가리키는 곳 %d군데(%s)' % (sn, c, a))
        for tbl in sec.iter(P('tbl')):
            ntbl += 1
            try:
                R = int(tbl.get('rowCnt'))
                Cn = int(tbl.get('colCnt'))
            except Exception:
                errs.append('표에 행·열 수가 없습니다.')
                continue
            trs = tbl.findall(P('tr'))
            if len(trs) != R:
                errs.append('표 %d: 행 수(%d)와 실제 줄(%d)이 다릅니다.' % (ntbl, R, len(trs)))
                continue
            occ = [[0] * Cn for _ in range(R)]
            okk = True
            for tr in trs:
                for tc in tr.findall(P('tc')):
                    ad = tc.find(P('cellAddr'))
                    r0, c0 = int(ad.get('rowAddr')), int(ad.get('colAddr'))
                    cs, rs = tc_span(tc)
                    for rr in range(r0, r0 + rs):
                        for cc in range(c0, c0 + cs):
                            if rr >= R or cc >= Cn:
                                okk = False
                            else:
                                occ[rr][cc] += 1
            if not okk or any(v != 1 for row in occ for v in row):
                errs.append('표 %d: 칸 배치가 어긋났습니다(겹치거나 빈 칸).' % ntbl)
        for p in sec.iter(P('p')):
            npara += 1
            s = para_text(p)
            if s.strip():
                text_all.append(s)
    full = '\n'.join(text_all)
    tips += lint_text(full)
    pi = scan_personal(full)
    if pi:
        tips.append('개인정보로 보이는 글자가 있습니다(%s). 보내기 전에 꼭 확인하세요.' % ', '.join(pi))
    head = '[점검] %s — 문단 %d개 · 표 %d개 · 글자 %d자' % (os.path.basename(path), npara, ntbl, len(full))
    try:
        n, fill, saved = gauge_pages(pkg)
        head += ' · %d쪽(한글이 저장한 쪽 나눔)' % saved if saved else ' · 약 %d쪽(어림)' % n
    except Exception:
        n = None
    L = [head]
    if errs:
        L.append('- 오류(한글에서 안 열릴 수 있음):')
        L += ['   · ' + e for e in errs[:12]]
    else:
        L.append('- 파일 구조: 이상 없음')
    for t in tips:
        L.append('- 확인: ' + t)
    out = '\n'.join(L)
    if not quiet:
        print(out)
    return out


# ---------------------------------------------------------------- 칸 채우기(신청서·서식)

def _walk_slots(root):
    """(키, 요소, 종류, 글자) 목록. P<n>=본문 문단, T<표>.<행>.<열>=표 칸."""
    out = []
    tno = [0]

    def walk_table(tbl):
        tno[0] += 1
        k = tno[0]
        for tr in tbl.findall(P('tr')):
            for tc in tr.findall(P('tc')):
                ad = tc.find(P('cellAddr'))
                key = 'T%d.%s.%s' % (k, ad.get('rowAddr'), ad.get('colAddr'))
                out.append((key, tc, 'cell', tc_text(tc)))
                sub = tc.find(P('subList'))
                if sub is not None:
                    for p in sub.findall(P('p')):
                        for r in para_runs(p):
                            for c in r:
                                if c.tag == P('tbl'):
                                    walk_table(c)

    for i, p in enumerate(c for c in root if c.tag == P('p')):
        txt = para_text(p)
        out.append(('P%d' % i, p, 'para', txt))
        for r in para_runs(p):
            for c in r:
                if c.tag == P('tbl'):
                    walk_table(c)
    return out


def slots(path, quiet=False, limit=400):
    pkg = Package(path)
    sec = pkg.xml(pkg.section_names()[0])
    items = _walk_slots(sec)
    L = ['[칸 목록] %s — 값.json에 {"키": "넣을 글자"}로 적어 fill 하세요. 빈칸 옆 ← 는 이웃 칸 글자(무슨 칸인지 힌트). '
         '사진이 들어갈 칸은 값을 "[사진]"으로' % os.path.basename(path)]
    cells = {}
    for key, el, kind, txt in items:
        if kind == 'cell':
            t, r, c = key[1:].split('.')
            cells[(t, int(r), int(c))] = txt
    count = 0
    for key, el, kind, txt in items:
        if count >= limit:
            L.append('… (이하 생략: 총 %d개)' % len(items))
            break
        shown = txt.replace('\n', ' / ').strip()
        if kind == 'para':
            if not shown:
                continue
            L.append('%-10s %s' % (key, shown[:70]))
        else:
            t, r, c = key[1:].split('.')
            r, c = int(r), int(c)
            hint = ''
            if not shown and photo_cell(el):
                shown = '(사진 칸 — 새 사진 자리로 쓰려면 값을 [사진]으로)'
            elif not shown:
                left = next((cells.get((t, r, cc)) for cc in range(c - 1, -1, -1) if cells.get((t, r, cc), '').strip()), '')
                up = next((cells.get((t, rr, c)) for rr in range(r - 1, -1, -1) if cells.get((t, rr, c), '').strip()), '')
                hint = '  ← ' + ' / '.join(x.replace('\n', ' ')[:20] for x in (left, up) if x)
                shown = '(빈칸)'
            L.append('%-10s %s%s' % (key, shown[:60], hint))
        count += 1
    out = '\n'.join(L)
    if not quiet:
        print(out)
    return out


def fill(path, values, out_path, quiet=False):
    """칸 채우기. values: dict 또는 JSON 파일 경로. 키: P<n>, T<표>.<행>.<열>, 찾기:<옛 글자>"""
    if isinstance(values, str):
        with open(values, encoding='utf-8-sig') as f:
            values = json.load(f)
    pkg = Package(path)
    sec_name = pkg.section_names()[0]
    sec = pkg.xml(sec_name)
    order = [k for k, el, kind, _ in _walk_slots(sec)]
    items = {k: (el, kind) for k, el, kind, _ in _walk_slots(sec)}
    hed = HeaderEditor(pkg)
    warns = []
    done = 0
    # [사진] 값은 문서에 나오는 차례대로 [사진1], [사진2] … 번호를 붙인다
    pk = sorted((k for k, v in values.items() if PHOTO_RE.match(str(v or '')) and k in items
                 and items[k][1] == 'cell'), key=order.index)
    values = dict(values)
    for n, k in enumerate(pk, 1):
        values[k] = '[사진%d]' % n
    for key, val in values.items():
        val = '' if val is None else str(val)
        if key.startswith(('찾기:', 'find:')):
            old = key.split(':', 1)[1]
            n = replace_in(sec, old, val)
            if not n:
                warns.append('"%s"를 찾지 못했습니다.' % old)
            done += bool(n)
            continue
        if key not in items:
            warns.append('없는 칸: %s' % key)
            continue
        el, kind = items[key]
        if kind == 'cell':
            set_cell_text(el, val)
            if key in pk:
                tr = el.getparent()
                if tr is not None and tr.getparent() is not None:
                    photo_frames(tr.getparent(), hed)
            # 빈칸에 남아 있던 연한 회색 안내 글자 모양을 물려받으면 채운 글이 흐리게 나온다
            if not hed.dark_fill(el.get('borderFillIDRef')):
                ink_runs(_tc_paras(el), hed)
            w, h = tc_size(el)
            if w and disp_len(val) > max(4, w / 1100.0) * 3:
                warns.append('%s: 칸에 비해 글이 길어 칸이 늘어날 수 있습니다.' % key)
        else:
            old = para_text(el)
            lead, g, trail, rest = split_marker(old)
            nl, ng, nt, nrest = split_marker(val)
            if g and not ng:
                a = len(lead) + len(g) + len(trail)
                fill_para(el, a, a, lead + g + trail, '', val.strip())
            else:
                fill_para(el, len(lead), len(lead), lead, '', val.strip())
            ink_runs([el], hed)
        done += 1
    hed.save()
    finish_package(pkg, sec_name, sec, None)
    pkg.save(out_path)
    rep = check(out_path, quiet=True)
    if pk:
        warns.append('사진 자리 %d개([사진1]~[사진%d])를 만들었습니다. 사용자에게 "개인정보 가리개의 [사진 넣기]에 이 파일과 사진을 '
                     '함께 끌어다 놓으면 차례로 들어갑니다"라고 알리세요.' % (len(pk), len(pk)))
    msg = ['[채우기 완료] %s — %d칸 채움' % (out_path, done)] + ['- 참고: ' + w for w in warns] + [rep]
    out = '\n'.join(msg)
    if not quiet:
        print(out)
    return out


# ---------------------------------------------------------------- 글자 꺼내기(.hwpx / .hwp)

def hwpx_text(path):
    pkg = Package(path)
    lines = []

    def walk(p):
        s = para_text(p)
        if s.strip():
            lines.append(s.rstrip())
        for r in para_runs(p):
            for c in r:
                if c.tag == P('tbl'):
                    for tr in c.findall(P('tr')):
                        cells = []
                        for tc in tr.findall(P('tc')):
                            cells.append(tc_text(tc).replace('\n', ' / '))
                        lines.append('| ' + ' | '.join(cells) + ' |')
                elif local(c.tag) in OBJ_LOCAL:
                    for t in c.iter(P('t')):
                        if t_text(t).strip():
                            lines.append('[도형 글자] ' + t_text(t).strip())
    for sn in pkg.section_names():
        for p in pkg.xml(sn).findall(P('p')):
            walk(p)
    return '\n'.join(lines)


class CFB:
    """한글 .hwp(복합 문서) 읽기 — 외부 패키지 없이 필요한 만큼만."""
    END = 0xFFFFFFFA

    def __init__(self, data):
        if data[:8] != b'\xd0\xcf\x11\xe0\xa1\xb1\x1a\xe1':
            raise HwpError('한글 .hwp 파일이 아닙니다.')
        self.d = data
        self.ss = 1 << struct.unpack_from('<H', data, 30)[0]
        self.mss = 1 << struct.unpack_from('<H', data, 32)[0]
        n_fat = struct.unpack_from('<I', data, 44)[0]
        dir_start = struct.unpack_from('<I', data, 48)[0]
        self.cutoff = struct.unpack_from('<I', data, 56)[0]
        mf_start = struct.unpack_from('<I', data, 60)[0]
        n_mf = struct.unpack_from('<I', data, 64)[0]
        difat_start = struct.unpack_from('<I', data, 68)[0]
        n_difat = struct.unpack_from('<I', data, 72)[0]
        difat = list(struct.unpack_from('<109I', data, 76))
        s = difat_start
        for _ in range(n_difat):
            if s >= self.END:
                break
            vals = struct.unpack('<%dI' % (self.ss // 4), self._sec(s))
            difat.extend(vals[:-1])
            s = vals[-1]
        self.fat = []
        for fs in [x for x in difat if x < self.END][:n_fat]:
            self.fat.extend(struct.unpack('<%dI' % (self.ss // 4), self._sec(fs)))
        dd = self._chain(dir_start)
        self.ent = []
        for i in range(len(dd) // 128):
            e = dd[i * 128:(i + 1) * 128]
            nl = struct.unpack_from('<H', e, 64)[0]
            self.ent.append({
                'name': e[:max(0, nl - 2)].decode('utf-16-le', 'ignore'), 'type': e[66],
                'left': struct.unpack_from('<I', e, 68)[0], 'right': struct.unpack_from('<I', e, 72)[0],
                'child': struct.unpack_from('<I', e, 76)[0], 'start': struct.unpack_from('<I', e, 116)[0],
                'size': struct.unpack_from('<Q', e, 120)[0] & (0xFFFFFFFF if self.ss == 512 else 0xFFFFFFFFFFFFFFFF),
            })
        root = self.ent[0]
        self.mini = self._chain(root['start'])[:root['size']] if root['start'] < self.END else b''
        self.minifat = []
        if n_mf and mf_start < self.END:
            mf = self._chain(mf_start)
            self.minifat = list(struct.unpack('<%dI' % (len(mf) // 4), mf))
        self.paths = {}
        self._walk(root['child'], '')

    def _sec(self, i):
        off = (i + 1) * self.ss
        return self.d[off:off + self.ss]

    def _chain(self, s):
        out = []
        seen = set()
        while s < self.END and s not in seen and s < len(self.fat):
            seen.add(s)
            out.append(self._sec(s))
            s = self.fat[s]
        return b''.join(out)

    def _minichain(self, s):
        out = []
        seen = set()
        while s < self.END and s not in seen and s < len(self.minifat):
            seen.add(s)
            out.append(self.mini[s * self.mss:(s + 1) * self.mss])
            s = self.minifat[s]
        return b''.join(out)

    def _walk(self, idx, prefix, depth=0):
        stack = [idx]
        seen = set()
        while stack:
            i = stack.pop()
            if i >= self.END or i >= len(self.ent) or i in seen:
                continue
            seen.add(i)
            e = self.ent[i]
            stack += [e['left'], e['right']]
            path = prefix + e['name']
            if e['type'] == 2:
                self.paths[path] = i
            elif e['type'] == 1 and depth < 8:
                self._walk(e['child'], path + '/', depth + 1)

    def read(self, path):
        e = self.ent[self.paths[path]]
        if e['size'] < self.cutoff:
            return self._minichain(e['start'])[:e['size']]
        return self._chain(e['start'])[:e['size']]


def _para_text_hwp(b):
    units = []
    i = 0
    n = len(b) // 2
    while i < n:
        c = struct.unpack_from('<H', b, i * 2)[0]
        if c >= 32:
            units.append(c)
            i += 1
        elif c in (10,):
            units.append(10)
            i += 1
        elif c in (0, 13, 24, 25, 26, 27, 28, 29):
            i += 1
        elif c in (30, 31):
            units.append(32)
            i += 1
        elif c == 9:
            units.append(9)
            i += 8
        else:
            i += 8
    return struct.pack('<%dH' % len(units), *units).decode('utf-16-le', 'replace')


def hwp_text(path):
    with open(path, 'rb') as f:
        data = f.read()
    cfb = CFB(data)
    if 'FileHeader' not in cfb.paths:
        raise HwpError('한글 문서 머리 정보가 없습니다.')
    fh = cfb.read('FileHeader')
    flags = struct.unpack_from('<I', fh, 36)[0]
    if flags & 2:
        raise HwpError('암호가 걸린 문서라 읽을 수 없습니다.')
    secs = sorted([p for p in cfb.paths if re.match(r'BodyText/Section\d+$', p)], key=lambda s: int(s[16:]))
    if (flags & 4) or not secs:
        raise HwpError('배포용(편집 제한) 문서라 글자를 꺼낼 수 없습니다. 한글에서 PDF로 저장해 올려 주세요.')
    out = []
    for s in secs:
        raw = cfb.read(s)
        if flags & 1:
            raw = zlib.decompress(raw, -15)
        pos = 0
        while pos + 4 <= len(raw):
            h = struct.unpack_from('<I', raw, pos)[0]
            pos += 4
            tag = h & 0x3FF
            size = (h >> 20) & 0xFFF
            if size == 0xFFF:
                size = struct.unpack_from('<I', raw, pos)[0]
                pos += 4
            if tag == 67:
                t = _para_text_hwp(raw[pos:pos + size]).rstrip()
                if t.strip():
                    out.append(t)
            pos += size
    return '\n'.join(out)


def text(path, quiet=False):
    with open(path, 'rb') as f:
        head = f.read(8)
    if head == b'\xd0\xcf\x11\xe0\xa1\xb1\x1a\xe1':
        out = hwp_text(path)
    else:
        out = hwpx_text(path)
    if not quiet:
        print(out)
    return out


# ---------------------------------------------------------------- 분석(진입점)

def analyze(path, outline_path=None, quiet=False, max_lines=400):
    doc = RefDoc(path)
    ol = doc.outline()
    if outline_path is None:
        stem = os.path.splitext(os.path.basename(path))[0]
        d = os.path.dirname(os.path.abspath(path))
        if not os.access(d, os.W_OK):
            d = os.getcwd()
        outline_path = os.path.join(d, stem + '_개요.txt')
    with open(outline_path, 'w', encoding='utf-8') as f:
        f.write(ol)
    lines = ol.splitlines()
    shown = '\n'.join(lines[:max_lines]) + ('\n… (개요 %d줄 중 %d줄만 표시)' % (len(lines), max_lines) if len(lines) > max_lines else '')
    out = doc.summary() + '\n- 개요 파일: %s\n\n%s' % (outline_path, shown)
    if not quiet:
        print(out)
    return out


def main(argv=None):
    ap = argparse.ArgumentParser(description='한글(HWPX) 문서 자동 작성 엔진 v%s' % VERSION)
    sp = ap.add_subparsers(dest='cmd')
    a = sp.add_parser('analyze', help='양식 분석 + 개요 꺼내기')
    a.add_argument('hwpx')
    a.add_argument('-o', '--outline')
    b = sp.add_parser('build', help='개요대로 새 문서 만들기')
    b.add_argument('hwpx')
    b.add_argument('outline')
    b.add_argument('-o', '--out', required=True)
    s = sp.add_parser('slots', help='칸 목록')
    s.add_argument('hwpx')
    f = sp.add_parser('fill', help='칸 채우기')
    f.add_argument('hwpx')
    f.add_argument('values')
    f.add_argument('-o', '--out', required=True)
    c = sp.add_parser('check', help='결과 점검')
    c.add_argument('hwpx')
    t = sp.add_parser('text', help='글자 꺼내기(.hwpx/.hwp)')
    t.add_argument('file')
    args = ap.parse_args(argv)
    try:
        if args.cmd == 'analyze':
            analyze(args.hwpx, args.outline)
        elif args.cmd == 'build':
            build(args.hwpx, args.outline, args.out)
        elif args.cmd == 'slots':
            slots(args.hwpx)
        elif args.cmd == 'fill':
            fill(args.hwpx, args.values, args.out)
        elif args.cmd == 'check':
            check(args.hwpx)
        elif args.cmd == 'text':
            text(args.file)
        else:
            ap.print_help()
            return 1
    except HwpError as e:
        print('[안내] %s' % e)
        return 2
    except Exception as e:  # 예상 못 한 문제: 원인 파악용 정보는 남긴다
        import traceback
        traceback.print_exc()
        print('[오류] 처리 중 문제가 생겼습니다(%s: %s). 다른 양식으로 해 보거나, 개요를 더 단순하게 '
              '바꿔 다시 시도하세요.' % (type(e).__name__, e))
        return 3
    return 0


if __name__ == '__main__':
    sys.exit(main())
