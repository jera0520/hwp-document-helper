# 한글 문서 도우미

쓰던 한글(HWP/HWPX) 양식의 디자인은 그대로 두고 내용만 채워 주는 Claude 스킬과, 내 컴퓨터 안에서 이름·전화번호를 가리는 「개인정보 가리개」입니다.

- 내려받기 페이지(파일과 안내문): https://jera0520.github.io/hwp-document-helper/
- 최신판: 1.2판 (2026. 10. 14.)
- 만든 사람: 김진현(AI한술)

## 들어 있는 것

| 폴더·파일 | 내용 |
|---|---|
| `hwp-document-helper/` | Claude 스킬 원본. 내려받기 페이지의 `hwp-document-helper.zip`을 푼 것과 같습니다. |
| `hwp-document-helper/SKILL.md` | Claude가 읽는 사용법(질문 순서, 칸 채우기, 분량 맞추기, 점검) |
| `hwp-document-helper/scripts/hwpdoc.py` | 한글 파일을 읽고 만드는 엔진(파이썬 파일 하나, 파이썬 3.9 이상과 lxml 필요) |
| `hwp-document-helper/templates/` | 양식이 없을 때 쓰는 기본 보고서 틀 |
| `hwp-document-helper/reference/` | 공문 표기 기준, 개요 문법, 문서 종류별 구성 |
| `masker/개인정보_가리개.html` | 개인정보 가리개. 파일 하나라 인터넷 없이 열리고, 완성된 문서에 사진을 넣는 것도 여기서 합니다. |
| `docs/` | 내려받기 페이지 |

## 쓰는 법

1. claude.ai/settings/capabilities 에서 「코드 실행 및 파일 생성」을 켭니다.
2. 내려받기 페이지에서 `hwp-document-helper.zip`을 받아, 압축을 풀지 말고 claude.ai/customize/skills → 「Skill 추가」 → 「Skill 업로드」로 올립니다.
3. 채팅창에 쓰던 양식(.hwpx)을 올리고 「이 양식으로 ○○ 결과 보고 써 줘」처럼 부탁합니다.

Claude Code에서는 `hwp-document-helper` 폴더를 `~/.claude/skills/` 아래에 넣으면 됩니다. 자세한 순서는 내려받기 페이지의 한 장 안내문과 상세 안내문에 있습니다.

## 엔진만 따로 쓰기

```
python hwpdoc.py analyze 양식.hwpx -o 개요.txt        # 양식 분석, 지금 내용을 개요로 꺼내기
python hwpdoc.py build   양식.hwpx 개요.txt -o 결과.hwpx  # 개요대로 같은 디자인의 새 문서
python hwpdoc.py slots   양식.hwpx                       # 칸 목록(서식 칸 채우기용)
python hwpdoc.py fill    양식.hwpx 값.json -o 결과.hwpx   # 칸만 채우기
python hwpdoc.py check   결과.hwpx                       # 결과 점검
```

고친 내역은 내려받기 페이지 아래 「바뀐 내용」에 있습니다.
