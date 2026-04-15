#!/usr/bin/env python3

# bolls.py - Python client for bolls.life API

import hashlib
import json
import os
import re
import sys
import tempfile
import time
from io import BytesIO

try:
    import pycurl
except Exception as exc:
    print(f"Error: pycurl is required: {exc}", file=sys.stderr)
    sys.exit(2)

try:
    import jq as jqmod
except Exception:
    jqmod = None

BASE_URL = "https://bolls.life"
PARALLEL_CHAPTER_MAX_VERSE = 300
OUTPUT_LINE_THRESHOLD = 1000
OUTPUT_FILE_PREFIX = "bolls_output"
LOCAL_TRANSLATIONS_DIR = "bible-translations"
SOFT_LINK_PROBE_CHAPTER = 1
SOFT_LINK_PROBE_VERSE = 1
_MAX_VERSE_CACHE: dict[tuple[str, int, int], int] = {}
_SOFT_LINK_CACHE: dict[tuple[str, str], int] = {}
_LANGUAGE_MAP: dict[str, str] | None = None
_LANGUAGE_TRANSLATIONS: dict[str, set[str]] | None = None
_LOCAL_TRANSLATION_INDEX_CACHE: dict[str, dict[int, dict[int, list[dict]]]] = {}

JQ_PRETTY_FILTER = r"""

def indent($n): " " * ($n * 4);

def strip_html:
  if type == "string" then
    gsub("(?is)<s[^>]*>.*?</s>"; "")
    | gsub("<(br|p) */?>"; "\n")
    | gsub("<[^>]*>"; "")
  else . end;

def scalar:
  if . == null then "null"
  elif (type == "string") then (strip_html)
  else tostring
  end;

def is_scalar: (type == "string" or type == "number" or type == "boolean" or type == "null");

def keyfmt: gsub("_"; " ");

def fmt($v; $n):
  if ($v|type) == "object" then
    $v|to_entries|map(
      if (.value|type) == "object" or (.value|type) == "array" then
        "\(indent($n))\(.key|keyfmt):\n\(fmt(.value; $n+1))"
      else
        "\(indent($n))\(.key|keyfmt): \(.value|scalar)"
      end
    )|join("\n")
  elif ($v|type) == "array" then
    if ($v|length) == 0 then ""
    else
      ($v|map(fmt(.;$n))) as $lines
      | if ($v|all(is_scalar)) then ($lines|join("\n")) else ($lines|join("\n\n")) end
    end
  else
    "\(indent($n))\($v|scalar)"
  end;

fmt(.;0)

""".strip()

JQ_TEXT_COMMENT = r"""

def keep_text_comment:
  if type == "array" then map(keep_text_comment) | map(select(. != null and . != ""))
  elif type == "object" then
    if (has("comment") and .comment != null) then
      [ .text, {comment} ]
    else
      .text
    end
  else .
  end;

keep_text_comment

""".strip()

JQ_TEXT_ONLY = r"""

def keep_text_only:
  if type == "array" then map(keep_text_only) | map(select(. != null and . != ""))
  elif type == "object" then
    .text
  else .
  end;

keep_text_only

""".strip()


def _print_help() -> None:
    print("""
Command flags (choose one):
  -h / --help
  Show this help page

  -d / --dictionaries
  List all available Hebrew/Greek dictionaries

  -D / --define <dictionary> <Hebrew/Greek word>
  Get definitions for a Hebrew or Greek word

  -t / --translations
  List all available Bible translations

  -b / --books <translation>
  List all books of a chosen translation

  -v / --verses <translation(s)> <book> [chapter(s) [:verse(s)] ]
  Get text from the Bible

  -r / --random <translation>
  Get a single random verse

  -s / --search <translation> [options] <search term>
  Search text in verses

  Search options (choose any amount or none when using -s):
    -c / --match-case
    Make search case-sensitive

    -w / --match-whole
    Only search exact phrase matches (requires multiple words)

    -B / --book <book/ot/nt>
    Search in a specific book, or in just the Old or New Testament

    -p / --page <#>
    Go to a specific page of search results (each page has up to 128 results by default)

    -l / --page-limit <#>
    Limits the number of search results displayed per page


Notes:
  <translation> must be the abbreviation, not the full name. Multiple translations are separated by commas.

  <book> can be a number, full name, or short name (e.g. "1th" instead of "1 Thessalonians").

  [verse(s)] and [chapter(s)] can be a single number, multiple numbers separated by commas (e.g. 1,5,9), or a range (e.g. 13-17).

  When using -v, omit verses to get a full chapter, and omit chapters to get the full book.

  Use slashes to use multiple -v commands at once (see examples).


Modifier flags (choose one or none):
  -j / --raw-json
  Disable formatting

  -a / --include-all
  Include everything (verse id, translation, book number, etc.) in -v

  -C / --include-comments
  Include commentary (currently not working without -n)

  -f / --file
  Save output to a .txt or .json file in current working directory

  -n / --no-api
  Use local translation files for -v (downloads if missing)

  -u / --url
  Print the URL (and POST body) that would have been called from the API


Examples:
  bolls --dictionaries
  Lists all the available dictionaries.

  bolls -D BDBT אֹ֑ור 
  Translates אֹ֑ור to English using Brown-Driver-Briggs' Hebrew Definitions / Thayer's Greek Definitions.

  bolls --translations
  Lists all the available Bible translations.

  bolls -b AMP
  Lists the books in the Amplified translation.

  bolls --verses ESV genesis 1 --no-api --include-comments
  bolls -v esv 1 1 -n -C
  Shows the text of Genesis 1 from a downloaded copy of the English Standard Version, including commentary.

  bolls --verses nlt,nkjv exodus 2:1,5,7 -a
  Shows Exodus 2:1, 2:5, and 2:7 from both the New Living Translation and the New King James Version, with all the descriptive information.

  bolls -v niv jon 1:1-3 / esv luk 2 / ylt,nkjv deu 6:5
  Shows John 1:1-3 from the New International Version, Luke 2 from the English Standard Version, and Deuteronomy 6:5 from Young's Literal Translation and the New King James Version.

  bolls --verses niv 1 Corinthians
  Shows the entirety of 1 Corinthians from the New international Version.

  bolls -r MSG -j -f
  Shows a random verse from the Message translation in raw JSON format, and saves it to a file.

  bolls --random nlt -u
  Shows the URL that would have been used to get a random verse from the New Living Translation.

  bolls -s ylt -c -w -l 3 Jesus said
  bolls --search YLT --match-case --match-whole --page-limit 3 Jesus said
  Searches Young's Literal Translation for "Jesus said", case-sensitive and matching the entire phrase, with a limit of 3 results.
""".strip()
    )


def _curl_get(url: str) -> str:
    buf = BytesIO()
    curl = pycurl.Curl()
    try:
        curl.setopt(pycurl.URL, url)
        curl.setopt(pycurl.WRITEDATA, buf)
        curl.setopt(pycurl.FAILONERROR, True)
        curl.setopt(pycurl.NOSIGNAL, True)
        curl.perform()
    except pycurl.error as exc:
        errno, msg = exc.args
        print(f"Error: HTTP request failed ({errno}): {msg}", file=sys.stderr)
        raise
    finally:
        curl.close()
    return buf.getvalue().decode("utf-8", errors="replace")


def _curl_post(url: str, body: str) -> str:
    buf = BytesIO()
    curl = pycurl.Curl()
    try:
        curl.setopt(pycurl.URL, url)
        curl.setopt(pycurl.WRITEDATA, buf)
        curl.setopt(pycurl.FAILONERROR, True)
        curl.setopt(pycurl.NOSIGNAL, True)
        curl.setopt(pycurl.HTTPHEADER, ["Content-Type: application/json"])
        curl.setopt(pycurl.POSTFIELDS, body.encode("utf-8"))
        curl.perform()
    except pycurl.error as exc:
        errno, msg = exc.args
        print(f"Error: HTTP request failed ({errno}): {msg}", file=sys.stderr)
        raise
    finally:
        curl.close()
    return buf.getvalue().decode("utf-8", errors="replace")


def _jq_pretty(raw: str, jq_prefix: str | None) -> str:
    program = JQ_PRETTY_FILTER
    if jq_prefix:
        program = f"{jq_prefix}\n| {JQ_PRETTY_FILTER}"
    compiled = jqmod.compile(program)
    out = compiled.input_text(raw).first()
    if out is None:
        return ""
    if isinstance(out, (dict, list)):
        return json.dumps(out, indent=2, ensure_ascii=False)
    return str(out)

def _drop_translation_only_entries(value: object) -> object:
    if isinstance(value, list):
        out = []
        for item in value:
            cleaned = _drop_translation_only_entries(item)
            if cleaned is None:
                continue
            out.append(cleaned)
        return out
    if isinstance(value, dict):
        # Drop objects that only contain a translation and no text/meaningful fields
        if "translation" in value and "text" not in value:
            if all(k == "translation" for k in value.keys()):
                return None
        if "translation" in value and (value.get("text") is None or value.get("text") == ""):
            has_meaningful = False
            for k, v in value.items():
                if k in ("translation", "text"):
                    continue
                if v not in (None, "", [], {}):
                    has_meaningful = True
                    break
            if not has_meaningful:
                return None
        cleaned = {}
        for k, v in value.items():
            cleaned_v = _drop_translation_only_entries(v)
            if cleaned_v is None:
                continue
            cleaned[k] = cleaned_v
        return cleaned
    return value


def _strip_s_tags(text: str) -> str:
    return re.sub(r"<s[^>]*>.*?</s>", "", text, flags=re.IGNORECASE | re.DOTALL)


def _strip_s_tags_in_data(value: object) -> object:
    if isinstance(value, str):
        return _strip_s_tags(value)
    if isinstance(value, list):
        return [_strip_s_tags_in_data(v) for v in value]
    if isinstance(value, dict):
        return {k: _strip_s_tags_in_data(v) for k, v in value.items()}
    return value

def _strip_html(text: str) -> str:
    text = re.sub(r"(?is)<s[^>]*>.*?</s>", "", text)
    text = re.sub(r"(?i)<(br|p)\s*/?>", "\n", text)
    text = re.sub(r"<[^>]*>", "", text)
    return text


def _value_to_int(value: object) -> int | None:
    if isinstance(value, bool):
        return None
    if isinstance(value, int):
        return value
    if isinstance(value, str) and value.isdigit():
        return int(value)
    return None


def _get_chapter_value(item: dict) -> int | None:
    return _value_to_int(item.get("chapter"))


def _get_verse_value(item: dict) -> int | None:
    return _value_to_int(item.get("verse"))


def _get_book_value(item: dict) -> int | None:
    return _value_to_int(item.get("book"))


def _flatten_verse_items(data: object) -> list[dict]:
    out: list[dict] = []
    if isinstance(data, dict):
        out.append(data)
        return out
    if isinstance(data, list):
        for item in data:
            if isinstance(item, list):
                out.extend(_flatten_verse_items(item))
            elif isinstance(item, dict):
                out.append(item)
        return out
    return out


def _format_verses(raw: str, include_comments: bool) -> str | None:
    def render_items(items: list[dict]) -> str:
        parts: list[str] = []
        last_chapter: int | None = None
        for item in items:
            if not isinstance(item, dict):
                continue
            comment_val = item.get("comment") if include_comments else None
            text_val = item.get("text")
            if text_val is None:
                if include_comments and comment_val not in (None, ""):
                    text_val = ""
                else:
                    continue
            if not isinstance(text_val, str):
                text_val = str(text_val)
            text_val = _strip_html(text_val)

            verse_val = _get_verse_value(item)
            verse_prefix = f"[{verse_val}] " if verse_val is not None else ""

            if include_comments and comment_val not in (None, ""):
                if not isinstance(comment_val, str):
                    comment_val = str(comment_val)
                block = f"{verse_prefix}{text_val} [{comment_val}]\n\n"
            else:
                block = f"{verse_prefix}{text_val}"

            chapter_val = _get_chapter_value(item)
            if parts:
                if chapter_val is not None and last_chapter is not None and chapter_val != last_chapter:
                    parts.append("\n\n{name} {chapter_val}\n")
                else:
                    parts.append(" ")
            parts.append(block)
            if chapter_val is not None:
                last_chapter = chapter_val
        return "".join(parts)

    try:
        data = json.loads(raw)
    except Exception:
        return None

    blocks: list[str] = []
    if isinstance(data, list):
        has_nested = any(isinstance(item, list) for item in data)
        if has_nested:
            for group in data:
                if isinstance(group, list):
                    rendered = render_items(_flatten_verse_items(group))
                elif isinstance(group, dict):
                    rendered = render_items([group])
                else:
                    rendered = ""
                if rendered:
                    blocks.append(rendered)
        else:
            rendered = render_items(_flatten_verse_items(data))
            if rendered:
                blocks.append(rendered)
    else:
        rendered = render_items(_flatten_verse_items(data))
        if rendered:
            blocks.append(rendered)

    if not blocks:
        return None

    out = "\n\n".join(blocks)
    if out and not out.endswith("\n"):
        out += "\n"
    return out

def _format_json(
    raw: str,
    raw_json: bool,
    jq_prefix: str | None = None,
    drop_translation_only: bool = False,
) -> str:
    if drop_translation_only:
        try:
            data = json.loads(raw)
        except Exception:
            data = None
        if data is not None:
            data = _drop_translation_only_entries(data)
            raw = json.dumps(data, ensure_ascii=False)
    if raw_json:
        return raw
    if jqmod is not None:
        try:
            rendered = _jq_pretty(raw, jq_prefix)
            if rendered and not rendered.endswith("\n"):
                rendered += "\n"
            return rendered
        except Exception:
            pass
    try:
        data = json.loads(raw)
    except Exception:
        return raw
    data = _strip_s_tags_in_data(data)
    return json.dumps(data, indent=2, ensure_ascii=False) + "\n"


def _print_json(
    raw: str,
    raw_json: bool,
    jq_prefix: str | None = None,
    drop_translation_only: bool = False,
) -> None:
    sys.stdout.write(_format_json(raw, raw_json, jq_prefix, drop_translation_only))


def _line_count(text: str) -> int:
    if not text:
        return 0
    return len(text.splitlines())


def _next_output_path(ext: str) -> str:
    ts = time.strftime("%Y%m%d_%H%M%S")
    base = f"{OUTPUT_FILE_PREFIX}_{ts}"
    directory = os.getcwd()
    path = os.path.join(directory, f"{base}.{ext}")
    if not os.path.exists(path):
        return path
    for i in range(1, 1000):
        alt = os.path.join(directory, f"{base}_{i}.{ext}")
        if not os.path.exists(alt):
            return alt
    return os.path.join(directory, f"{base}_{int(time.time())}.{ext}")


def _save_output(text: str, raw_json: bool) -> str:
    ext = "json" if raw_json else "txt"
    path = _next_output_path(ext)
    with open(path, "w", encoding="utf-8") as f:
        f.write(text)
    return path


def _write_output(text: str, raw_json: bool, force_file: bool) -> None:
    sys.stdout.write(text)
    line_count = _line_count(text)
    if force_file or line_count > OUTPUT_LINE_THRESHOLD:
        path = _save_output(text, raw_json)
        print(f"Saved output to {path}", file=sys.stderr)


def _format_url(method: str, url: str, body: str | None = None) -> str:
    method_up = method.upper()
    if method_up == "POST" and body is not None:
        body_out = body.rstrip("\n")
        return f"{method_up} {url}\n{body_out}\n"
    return f"{method_up} {url}\n"

def _split_slash_groups(args: list[str]) -> list[list[str]]:
    groups = []
    current = []
    for token in args:
        if token == "/":
            if current:
                groups.append(current)
                current = []
            continue
        if "/" not in token or token.startswith("/") or token.startswith("./") or token.startswith("../"):
            current.append(token)
            continue
        parts = token.split("/")
        for i, part in enumerate(parts):
            part = part.strip()
            if part:
                current.append(part)
            if i < len(parts) - 1:
                if current:
                    groups.append(current)
                    current = []
    if current:
        groups.append(current)
    return groups


def _is_single_chapter_book_for_translation(translation: str, book: str) -> bool:
    try:
        book_id = _book_to_id(
            translation,
            book,
            allow_language_fallback=True,
        )
    except Exception:
        return False

    try:
        data = _load_books_data()
    except Exception:
        return False

    keys = {k.lower(): k for k in data.keys()}
    tkey = translation.lower()
    if tkey not in keys:
        return False

    entry = None
    for item in data[keys[tkey]]:
        if isinstance(item, dict) and item.get("bookid") == book_id:
            entry = item
            break

    chapters = _chapters_from_entry(entry)
    return bool(chapters and len(chapters) == 1)


def _group_translation_info(group: list[str]) -> tuple[set[str], bool]:
    if not group:
        return set(), False
    if len(group) < 2:
        return set(), False
    translations = set(_parse_translations_arg(group[0]))
    ref_args = group[1:]
    if not ref_args:
        return translations, False
    mode, book, chapters, _ = _parse_v_reference(ref_args)
    if mode == "book":
        is_multi_chapter = any(
            not _is_single_chapter_book_for_translation(translation, book)
            for translation in translations
        )
        return translations, is_multi_chapter
    if mode == "chapters":
        return translations, bool(chapters and len(chapters) > 1)
    return translations, False


def _is_local_translation_cached(translation: str) -> bool:
    cache_path = _local_translation_cache_path(translation)
    return os.path.isfile(cache_path) and os.path.getsize(cache_path) > 0


def _should_default_no_api_for_group(group: list[str]) -> bool:
    translations, is_multi_chapter = _group_translation_info(group)
    return is_multi_chapter and len(translations) == 1


def _enforce_no_api_download_limit(groups: list[list[str]], no_api_requested: bool) -> None:
    no_api_translations: set[str] = set()
    for group in groups:
        translations, _ = _group_translation_info(group)
        effective_no_api = no_api_requested or _should_default_no_api_for_group(group)
        if effective_no_api:
            no_api_translations.update(t.upper() for t in translations)

    if len(no_api_translations) <= 1:
        return

    uncached = sorted(t for t in no_api_translations if not _is_local_translation_cached(t))
    if len(uncached) > 1:
        missing = ", ".join(uncached)
        raise ValueError(
            "Refusing request: this would require downloading multiple uncached translations "
            f"({missing}). Download those translations manually, or use separate commands for this request."
        )

def _local_translation_cache_dir() -> str:
    return os.path.join(os.getcwd(), LOCAL_TRANSLATIONS_DIR)


def _local_translation_cache_path(translation: str) -> str:
    return os.path.join(_local_translation_cache_dir(), f"{translation.upper()}.json")


def _local_sections_cache_dir(translation: str) -> str:
    return os.path.join(_local_translation_cache_dir(), "sections", translation.upper())


def _ensure_local_translation_cache(translation: str) -> str:
    translation_up = translation.upper()
    cache_dir = _local_translation_cache_dir()
    os.makedirs(cache_dir, exist_ok=True)
    cache_path = _local_translation_cache_path(translation_up)
    if os.path.isfile(cache_path) and os.path.getsize(cache_path) > 0:
        return cache_path
    url = f"{BASE_URL}/static/translations/{translation_up}.json"
    raw = _curl_get(url)
    _validate_json(raw)
    with open(cache_path, "w", encoding="utf-8") as f:
        f.write(raw)
    return cache_path


def _collect_translation_verse_items(data: object, translation: str) -> list[dict]:
    out: list[dict] = []

    def walk(node: object) -> None:
        if isinstance(node, list):
            for child in node:
                walk(child)
            return
        if not isinstance(node, dict):
            return
        book_val = _get_book_value(node)
        chapter_val = _get_chapter_value(node)
        text_val = node.get("text")
        comment_val = node.get("comment")
        has_content = text_val not in (None, "") or comment_val not in (None, "")
        if book_val is not None and chapter_val is not None and has_content:
            verse_obj = dict(node)
            if not isinstance(verse_obj.get("translation"), str):
                verse_obj["translation"] = translation.upper()
            out.append(verse_obj)
            return
        for child in node.values():
            if isinstance(child, (list, dict)):
                walk(child)

    walk(data)
    return out


def _translation_chapter_index(translation: str) -> dict[int, dict[int, list[dict]]]:
    translation_up = translation.upper()
    cached = _LOCAL_TRANSLATION_INDEX_CACHE.get(translation_up)
    if cached is not None:
        return cached
    cache_path = _ensure_local_translation_cache(translation_up)
    with open(cache_path, "r", encoding="utf-8") as f:
        data = json.load(f)
    verses = _collect_translation_verse_items(data, translation_up)
    index: dict[int, dict[int, list[dict]]] = {}
    for item in verses:
        book_val = _get_book_value(item)
        chapter_val = _get_chapter_value(item)
        if book_val is None or chapter_val is None:
            continue
        index.setdefault(book_val, {}).setdefault(chapter_val, []).append(item)
    for chapters in index.values():
        for chapter_num, chapter_items in list(chapters.items()):
            chapters[chapter_num] = sorted(
                chapter_items,
                key=lambda v: (_get_verse_value(v) is None, _get_verse_value(v) or 0),
            )
    _LOCAL_TRANSLATION_INDEX_CACHE[translation_up] = index
    return index


def _local_chapters_for_book(translation: str, book_id: int) -> list[int]:
    index = _translation_chapter_index(translation)
    chapters = index.get(int(book_id), {})
    return sorted(chapters.keys())


def _local_verses_for_chapter(translation: str, book_id: int, chapter: int) -> list[int]:
    index = _translation_chapter_index(translation)
    chapter_items = index.get(int(book_id), {}).get(int(chapter), [])
    out: list[int] = []
    seen: set[int] = set()
    for item in chapter_items:
        verse_num = _get_verse_value(item)
        if verse_num is None or verse_num in seen:
            continue
        seen.add(verse_num)
        out.append(verse_num)
    return out


def _section_cache_path(translation: str, request: dict) -> str:
    section_dir = _local_sections_cache_dir(translation)
    os.makedirs(section_dir, exist_ok=True)
    key = json.dumps(request, ensure_ascii=False, sort_keys=True, separators=(",", ":"))
    digest = hashlib.sha1(key.encode("utf-8")).hexdigest()
    return os.path.join(section_dir, f"{digest}.json")


def _build_local_section(translation: str, request: dict) -> list[dict]:
    index = _translation_chapter_index(translation)
    book_val = _value_to_int(request.get("book"))
    if book_val is None:
        return []
    chapters = index.get(book_val, {})
    if not chapters:
        return []

    chapter_raw = request.get("chapter")
    chapter_val = _value_to_int(chapter_raw)
    if chapter_raw is None:
        chapter_numbers = sorted(chapters.keys())
    elif chapter_val is None:
        return []
    elif chapter_val not in chapters:
        return []
    else:
        chapter_numbers = [chapter_val]

    verses_req = request.get("verses")
    verse_list: list[int] | None
    if verses_req is None:
        verse_list = None
    elif isinstance(verses_req, list):
        verse_list = []
        for value in verses_req:
            parsed = _value_to_int(value)
            if parsed is not None:
                verse_list.append(parsed)
    else:
        parsed = _value_to_int(verses_req)
        verse_list = [parsed] if parsed is not None else []

    out: list[dict] = []
    for chapter_number in chapter_numbers:
        chapter_items = chapters.get(chapter_number, [])
        if verse_list is None:
            selected = chapter_items
        else:
            by_verse: dict[int, list[dict]] = {}
            for item in chapter_items:
                verse_num = _get_verse_value(item)
                if verse_num is None:
                    continue
                by_verse.setdefault(verse_num, []).append(item)
            selected = []
            for verse_num in verse_list:
                selected.extend(by_verse.get(verse_num, []))
        for item in selected:
            out_item = dict(item)
            if not isinstance(out_item.get("translation"), str):
                out_item["translation"] = translation.upper()
            out.append(out_item)
    return out


def _load_local_section(translation: str, request: dict) -> list[dict]:
    cache_path = _section_cache_path(translation, request)
    if os.path.isfile(cache_path) and os.path.getsize(cache_path) > 0:
        try:
            with open(cache_path, "r", encoding="utf-8") as f:
                data = json.load(f)
            if isinstance(data, list):
                return data
        except Exception:
            pass
    section = _build_local_section(translation, request)
    with open(cache_path, "w", encoding="utf-8") as f:
        json.dump(section, f, ensure_ascii=False)
    return section


def _fetch_verses_from_local_cache(requests_obj: list[dict]) -> str:
    out: list[list[dict]] = []
    for req in requests_obj:
        if not isinstance(req, dict):
            out.append([])
            continue
        translation = req.get("translation")
        if not isinstance(translation, str) or not translation.strip():
            raise ValueError("get-verses items must include translation")
        translation = translation.upper()
        req_local = dict(req)
        req_local["translation"] = translation
        _ensure_local_translation_cache(translation)
        section = _load_local_section(translation, req_local)
        out.append(section)
    return json.dumps(out, ensure_ascii=False)


def _body_with_materialized_verses(requests_obj: list[dict]) -> str:
    body_obj_list: list[dict] = []
    for req in requests_obj:
        req_copy = dict(req)
        verses = req_copy.get("verses")
        if verses is None:
            translation = str(req_copy.get("translation", "")).upper()
            book_val = _value_to_int(req_copy.get("book"))
            chapter_val = _value_to_int(req_copy.get("chapter"))
            if translation and book_val is not None and chapter_val is not None:
                req_copy["verses"] = _local_verses_for_chapter(translation, book_val, chapter_val)
            else:
                req_copy["verses"] = []
        body_obj_list.append(req_copy)
    return json.dumps(body_obj_list)




def _build_verses_body_objects(rest: list[str], no_api: bool) -> list[dict]:
    if not rest:
        raise ValueError(
            "Error: Incorrect --verses syntax.\nUsage: bolls --verses <translation(s)> <book> [chapter(s) [:verse(s)] ]"
        )

    if len(rest) == 1:
        body = _normalize_get_verses_json(rest[0])
        obj = json.loads(body)
        if not isinstance(obj, list):
            raise ValueError("get-verses JSON must be an array")
        return obj

    translations_list = _parse_translations_arg(rest[0])
    ref_args = rest[1:]
    if not ref_args:
        raise ValueError(
            "Error: Incorrect --verses syntax.\nUsage: bolls --verses <translation(s)> <book> [chapter(s) [:verse(s)] ]"
        )
    mode, book, chapters, verses_list = _parse_v_reference(ref_args)

    body_obj_list: list[dict] = []
    for translation in translations_list:
        book_id = _book_to_id(
            translation,
            book,
            allow_language_fallback=True,
        )
        if mode == "book":
            if no_api:
                chapters_list = _local_chapters_for_book(translation, int(book_id))
            else:
                chapters_list = _chapters_for_book(translation, book_id)
            if not chapters_list:
                raise ValueError(
                    f"Could not determine chapters for book '{book}' in translation '{translation}'."
                )
        else:
            chapters_list = chapters or []

        for chapter_val in chapters_list:
            if mode == "verses":
                verses = verses_list
            elif no_api:
                verses = None
            else:
                max_verse = _max_verse_for_chapter(translation, book_id, chapter_val)
                verses = list(range(1, max_verse + 1))
            body_obj_list.append(
                {
                    "translation": translation,
                    "book": book_id,
                    "chapter": chapter_val,
                    "verses": verses,
                }
            )

    return body_obj_list

def _run_verses(
    rest: list[str],
    include_all: bool,
    add_comments: bool,
    raw_json: bool,
    url_only: bool = False,
    no_api: bool = False,
) -> str:
    jq_prefix = _choose_jq_prefix(include_all, add_comments)
    body_obj_list = _build_verses_body_objects(rest, no_api)

    if url_only:
        body_for_url = json.dumps(body_obj_list) if not no_api else _body_with_materialized_verses(body_obj_list)
        return _format_url("POST", f"{BASE_URL}/get-verses/", body_for_url)

    if no_api:
        raw = _fetch_verses_from_local_cache(body_obj_list)
    else:
        body = json.dumps(body_obj_list)
        raw = _curl_post(f"{BASE_URL}/get-verses/", body)

    if not raw_json and jq_prefix in (JQ_TEXT_ONLY, JQ_TEXT_COMMENT):
        formatted = _format_verses(raw, add_comments)
        if formatted is not None:
            return formatted
    return _format_json(raw, raw_json, jq_prefix, drop_translation_only=(include_all or raw_json))

def _norm_translation(s: str) -> str:
    return s.upper()

def _urlencode(s: str) -> str:
    from urllib.parse import quote

    return quote(s)


def _urlencode_path_segment(s: str) -> str:
    from urllib.parse import quote

    return quote(s, safe="")


def _soft_link_book_id(translation: str, book: str) -> int | None:
    if not isinstance(book, str):
        return None
    book = book.strip()
    if not book:
        return None
    t = translation.upper()
    key = (t, book.lower())
    cached = _SOFT_LINK_CACHE.get(key)
    if cached is not None:
        return cached
    book_enc = _urlencode_path_segment(book)
    url = (
        f"{BASE_URL}/get-verse/{t}/{book_enc}/"
        f"{SOFT_LINK_PROBE_CHAPTER}/{SOFT_LINK_PROBE_VERSE}/"
    )
    try:
        raw = _curl_get(url)
    except pycurl.error:
        return None
    try:
        data = json.loads(raw)
    except Exception:
        return None
    book_val = None
    if isinstance(data, dict):
        book_val = data.get("book")
    elif isinstance(data, list) and data:
        first = data[0]
        if isinstance(first, dict):
            book_val = first.get("book")
    if isinstance(book_val, str) and book_val.isdigit():
        book_val = int(book_val)
    if isinstance(book_val, int):
        _SOFT_LINK_CACHE[key] = book_val
        return book_val
    return None


def _choose_jq_prefix(include_all: bool, add_comments: bool) -> str | None:
    if include_all:
        return None
    if add_comments == False:
        return JQ_TEXT_ONLY
    return JQ_TEXT_COMMENT


def _json_array(raw: str, kind: str) -> str:
    s = raw.strip()
    if s.startswith("["):
        try:
            json.loads(s)
            return s
        except Exception:
            pass
    parts = []
    for chunk in s.split(","):
        chunk = chunk.strip()
        if not chunk:
            continue
        for piece in chunk.split():
            if piece:
                parts.append(piece)
    if kind == "int":
        vals = []
        for part in parts:
            try:
                vals.append(int(part))
            except Exception:
                raise ValueError(f"Invalid number in list: {part}")
        return json.dumps(vals)
    return json.dumps(parts)


def _parse_verses_spec(spec: str) -> list[int]:
    if not isinstance(spec, str):
        raise ValueError("Invalid verses list")
    spec = spec.strip()
    if not spec:
        raise ValueError("Invalid verses list")
    if spec.lstrip().startswith("["):
        try:
            data = json.loads(spec)
        except Exception as exc:
            raise ValueError(f"Invalid verses JSON: {exc}")
        if not isinstance(data, list):
            raise ValueError("Invalid verses JSON")
        out = []
        for item in data:
            if isinstance(item, int):
                out.append(item)
            elif isinstance(item, str) and item.isdigit():
                out.append(int(item))
            else:
                raise ValueError("Invalid verses JSON")
        return out
    parts = re.split(r"[,\s]+", spec)
    out = []
    for part in parts:
        if not part:
            continue
        m = re.fullmatch(r"(\d+)\s*[-–—]\s*(\d+)", part)
        if m:
            start = int(m.group(1))
            end = int(m.group(2))
            step = 1 if end >= start else -1
            out.extend(range(start, end + step, step))
            continue
        if not part.isdigit():
            raise ValueError(f"Invalid verse number: {part}")
        out.append(int(part))
    if not out:
        raise ValueError("Invalid verses list")
    return out



def _parse_chapters_spec(spec: str) -> list[int]:
    chapters = _parse_verses_spec(spec)
    for chapter in chapters:
        if chapter < 1:
            raise ValueError(f"Invalid chapter number: {chapter}")
    return chapters


def _parse_book_chapters(args: list[str]) -> tuple[str, list[int]]:
    if not args:
        raise ValueError("Error: Incorrect --verses syntax.\nUsage: bolls --verses <translation(s)> <book> [chapter(s) [:verse(s)] ]")
    joined = " ".join(args).strip()
    if not joined:
        raise ValueError("Missing book name")
    if joined.endswith("]"):
        idx = joined.rfind(" [")
        if idx != -1:
            book = joined[:idx].strip()
            chapters_spec = joined[idx + 1 :].strip()
            if not book:
                raise ValueError("Missing book name")
            chapters = _parse_chapters_spec(chapters_spec)
            return book, chapters
    match = re.match(r"^(?P<book>.+?)\s+(?P<chapters>[0-9][0-9\s,\-–—]*)$", joined)
    if not match:
        raise ValueError("Missing chapter list")
    book = match.group("book").strip()
    if not book:
        raise ValueError("Missing book name")
    chapters_spec = match.group("chapters").strip()
    chapters = _parse_chapters_spec(chapters_spec)
    return book, chapters
def _parse_book_chapter_verses(args: list[str]) -> tuple[str, int, list[int]]:
    if not args:
        raise ValueError("Error: Incorrect --verses syntax.\nUsage: bolls --verses <translation(s)> <book> [chapter(s) [:verse(s)] ]")
    joined = " ".join(args).strip()
    match = re.match(r"^(?P<book>.+?)\s+(?P<chapter>\d+)\s*:\s*(?P<verses>.+)$", joined)
    if match:
        book = match.group("book").strip()
        chapter_val = int(match.group("chapter"))
        verses_list = _parse_verses_spec(match.group("verses"))
        return book, chapter_val, verses_list
    if len(args) < 3:
        raise ValueError("Error: Incorrect --verses syntax.\nUsage: bolls --verses <translation(s)> <book> [chapter(s) [:verse(s)] ]")
    verses_arg = args[-1]
    chapter = args[-2]
    book = " ".join(args[:-2]).strip()
    if not book:
        raise ValueError("Missing book name")
    try:
        chapter_val = int(chapter)
    except ValueError:
        raise ValueError(f"Invalid chapter: {chapter}")
    if os.path.isfile(verses_arg):
        verses_json = _read_file(verses_arg)
        try:
            verses_list = json.loads(verses_json)
        except Exception as exc:
            raise ValueError(f"Invalid JSON: {exc}")
    else:
        verses_list = _parse_verses_spec(verses_arg)
    return book, chapter_val, verses_list

def _parse_book_chapter(args: list[str]) -> tuple[str, int]:
    if not args:
        raise ValueError("Error: Incorrect --verses syntax.\nUsage: bolls --verses <translation(s)> <book> [chapter(s) [:verse(s)] ]")
    joined = " ".join(args).strip()
    match = re.match(r"^(?P<book>.+?)\s+(?P<chapter>\d+)$", joined)
    if match:
        book = match.group("book").strip()
        chapter_val = int(match.group("chapter"))
        return book, chapter_val
    if len(args) < 2:
        raise ValueError("Error: Incorrect --verses syntax.\nUsage: bolls --verses <translation(s)> <book> [chapter(s) [:verse(s)] ]")
    chapter = args[-1]
    book = " ".join(args[:-1]).strip()
    if not book:
        raise ValueError("Missing book name")
    try:
        chapter_val = int(chapter)
    except ValueError:
        raise ValueError(f"Invalid chapter: {chapter}")
    return book, chapter_val


def _parse_translations_arg(arg: str) -> list[str]:
    if os.path.isfile(arg):
        translations_json = _read_file(arg)
    else:
        translations_json = _json_array(arg, "string")
    translations_json = _uppercase_translations(translations_json)
    try:
        translations_list = json.loads(translations_json)
    except Exception as exc:
        raise ValueError(f"Invalid JSON: {exc}")
    if not isinstance(translations_list, list) or not translations_list:
        raise ValueError("Translations list is empty!")
    return translations_list


def _parse_v_reference(args: list[str]) -> tuple[str, str, list[int] | None, list[int] | None]:
    if not args:
        raise ValueError("Error: Incorrect --verses syntax.\nUsage: bolls --verses <translation(s)> <book> [chapter(s) [:verse(s)] ]")
    if any(":" in a for a in args):
        book, chapter_val, verses_list = _parse_book_chapter_verses(args)
        return "verses", book, [chapter_val], verses_list
    joined = " ".join(args).strip()
    if not joined:
        raise ValueError("Missing book name")
    try:
        book, chapters = _parse_book_chapters(args)
        return "chapters", book, chapters, None
    except ValueError as exc:
        msg = str(exc)
        last = args[-1]
        if re.search(r"\d", last) and re.search(r"[A-Za-z]", last):
            raise ValueError(f"Invalid chapter list: {last}")
        if msg.startswith("Missing chapter list"):
            return "book", joined, None, None
        raise

def _max_verse_for_chapter(translation: str, book_id: int, chapter: int) -> int:
    cache_key = (translation.upper(), int(book_id), int(chapter))
    cached = _MAX_VERSE_CACHE.get(cache_key)
    if cached is not None:
        return cached
    limit = 32
    while True:
        verses = list(range(1, limit + 1))
        body = json.dumps(
            [
                {
                    "translation": translation,
                    "book": book_id,
                    "chapter": chapter,
                    "verses": verses,
                }
            ]
        )
        raw = _curl_post(f"{BASE_URL}/get-verses/", body)
        try:
            data = json.loads(raw)
        except Exception:
            _MAX_VERSE_CACHE[cache_key] = PARALLEL_CHAPTER_MAX_VERSE
            return PARALLEL_CHAPTER_MAX_VERSE
        verses_out = []
        if isinstance(data, list) and data:
            first = data[0]
            if isinstance(first, list):
                for item in first:
                    if isinstance(item, dict):
                        v = item.get("verse")
                        if isinstance(v, int):
                            verses_out.append(v)
        max_verse = max(verses_out) if verses_out else 0
        if max_verse < limit:
            _MAX_VERSE_CACHE[cache_key] = max_verse
            return max_verse
        if limit >= PARALLEL_CHAPTER_MAX_VERSE:
            _MAX_VERSE_CACHE[cache_key] = limit
            return limit
        limit = min(limit * 2, PARALLEL_CHAPTER_MAX_VERSE)


def _ensure_books_cache() -> str:
    cache = os.path.join(tempfile.gettempdir(), "bolls_translations_books.json")
    if not os.path.isfile(cache) or os.path.getsize(cache) == 0:
        raw = _curl_get(f"{BASE_URL}/static/bolls/app/views/translations_books.json")
        with open(cache, "w", encoding="utf-8") as f:
            f.write(raw)
    return cache


def _ensure_languages_cache() -> str:
    cache = os.path.join(tempfile.gettempdir(), "bolls_languages.json")
    if not os.path.isfile(cache) or os.path.getsize(cache) == 0:
        raw = _curl_get(f"{BASE_URL}/static/bolls/app/views/languages.json")
        with open(cache, "w", encoding="utf-8") as f:
            f.write(raw)
    return cache


def _load_books_data() -> dict:
    cache = _ensure_books_cache()
    with open(cache, "r", encoding="utf-8") as f:
        return json.load(f)



def _chapters_from_entry(entry: object) -> list[int] | None:
    if not isinstance(entry, dict):
        return None
    chapters = entry.get("chapters")
    if isinstance(chapters, int):
        return list(range(1, chapters + 1))
    if isinstance(chapters, str) and chapters.isdigit():
        return list(range(1, int(chapters) + 1))
    if isinstance(chapters, list):
        out: list[int] = []
        for item in chapters:
            parsed = _value_to_int(item)
            if parsed is not None:
                out.append(parsed)
        if out:
            return sorted(set(out))
        return []
    return None


def _probe_chapters_for_book(translation: str, book_id: int, max_chapters: int = 200) -> list[int]:
    chapters = []
    for chapter in range(1, max_chapters + 1):
        max_verse = _max_verse_for_chapter(translation, book_id, chapter)
        if max_verse <= 0:
            if chapter == 1:
                return []
            break
        chapters.append(chapter)
    return chapters


def _chapters_for_book(translation: str, book_id: int) -> list[int]:
    data = _load_books_data()
    keys = {k.lower(): k for k in data.keys()}
    tkey = translation.lower()
    if tkey not in keys:
        return []
    t = keys[tkey]
    entry = None
    for item in data[t]:
        if isinstance(item, dict) and item.get("bookid") == book_id:
            entry = item
            break
    chapters = _chapters_from_entry(entry)
    if chapters:
        return chapters
    return _probe_chapters_for_book(translation, book_id)
def _load_languages_data() -> object:
    cache = _ensure_languages_cache()
    with open(cache, "r", encoding="utf-8") as f:
        return json.load(f)

def _norm_language_name(name: str) -> str:
    return re.sub(r"[^a-z0-9]+", "", name.lower())

def _extract_translation_code(entry: object) -> str | None:
    if isinstance(entry, str):
        return entry.strip() or None
    if not isinstance(entry, dict):
        return None
    val = entry.get("short_name")
    if isinstance(val, str) and val.strip():
        return val.strip()
    return None

def _collect_language_maps(data: object) -> tuple[dict[str, str], dict[str, set[str]]]:
    translation_to_language: dict[str, str] = {}
    language_to_translations: dict[str, set[str]] = {}

    def add(code: str, language: str) -> None:
        if not code or not language:
            return
        code_up = code.upper()
        lang_norm = _norm_language_name(language)
        if not lang_norm:
            return
        translation_to_language[code_up] = lang_norm
        language_to_translations.setdefault(lang_norm, set()).add(code_up)

    def handle_language_block(language: object, translations: object) -> None:
        if not isinstance(language, str) or not language.strip():
            return
        if not isinstance(translations, list):
            return
        for entry in translations:
            code = _extract_translation_code(entry)
            if code:
                add(code, language)

    if isinstance(data, dict):
        # Supported documented-ish shapes:
        # 1) {"languages": [...]}
        # 2) {"English": [{"short_name": "YLT"}, ...], ...}
        languages_list = data.get("languages")
        if isinstance(languages_list, list):
            return _collect_language_maps(languages_list)
        if data and all(isinstance(v, list) for v in data.values()):
            for lang_name, trans_list in data.items():
                handle_language_block(lang_name, trans_list)
            return translation_to_language, language_to_translations

    if isinstance(data, list):
        for item in data:
            if not isinstance(item, dict):
                continue
            translations = item.get("translations")
            language = item.get("language")
            if isinstance(translations, list):
                handle_language_block(language, translations)
                continue
            code = _extract_translation_code(item)
            if code and isinstance(language, str) and language.strip():
                add(code, language)

    return translation_to_language, language_to_translations

def _get_language_maps() -> tuple[dict[str, str], dict[str, set[str]]]:
    global _LANGUAGE_MAP, _LANGUAGE_TRANSLATIONS
    if _LANGUAGE_MAP is not None and _LANGUAGE_TRANSLATIONS is not None:
        return _LANGUAGE_MAP, _LANGUAGE_TRANSLATIONS
    try:
        data = _load_languages_data()
    except Exception:
        _LANGUAGE_MAP = {}
        _LANGUAGE_TRANSLATIONS = {}
        return _LANGUAGE_MAP, _LANGUAGE_TRANSLATIONS
    t2l, l2t = _collect_language_maps(data)
    _LANGUAGE_MAP = t2l
    _LANGUAGE_TRANSLATIONS = l2t
    return _LANGUAGE_MAP, _LANGUAGE_TRANSLATIONS

def _find_book_in_translation(entries: object, target: str, norm) -> tuple[object | None, str | None]:
    if not isinstance(entries, list):
        return None, None
    candidates = []
    for entry in entries:
        if not isinstance(entry, dict):
            continue
        name = entry.get("name", "")
        n = norm(name)
        if n == target:
            return entry.get("bookid"), None
        if n.startswith(target):
            candidates.append(entry)
    if len(candidates) == 1:
        return candidates[0].get("bookid"), None
    if len(candidates) > 1:
        return None, "ambiguous"
    return None, None

def _book_id_from_language_fallback(
    translation_key: str, book: str, books_data: dict, norm
) -> tuple[object | None, bool]:
    t2l, l2t = _get_language_maps()
    if not t2l or not l2t:
        return None, False
    lang = t2l.get(translation_key.upper())
    if not lang:
        return None, False
    translations = l2t.get(lang, set())
    if not translations:
        return None, False
    keys = {k.lower(): k for k in books_data.keys()}
    found: dict[object, set[str]] = {}
    target = norm(book)
    for trans_code in translations:
        t_lower = trans_code.lower()
        if t_lower not in keys:
            continue
        t_actual = keys[t_lower]
        book_id, issue = _find_book_in_translation(books_data.get(t_actual), target, norm)
        if issue == "ambiguous":
            continue
        if book_id is not None:
            found.setdefault(book_id, set()).add(t_actual)
    if len(found) == 1:
        return next(iter(found)), True
    if len(found) > 1:
        ids = ", ".join(str(bid) for bid in sorted(found, key=lambda v: str(v)))
        raise ValueError(
            f"book name '{book}' matches multiple books across translations of the same language ({ids}). "
            "Try a more specific book name."
        )
    return None, True

def _book_to_id(
    translation: str,
    book: object,
    *,
    allow_language_fallback: bool = False,
) -> object:
    if isinstance(book, int):
        return book
    if isinstance(book, str) and book.isdigit():
        return int(book)
    if not isinstance(book, str):
        return book
    data = _load_books_data()
    keys = {k.lower(): k for k in data.keys()}
    tkey = translation.lower()
    if tkey not in keys:
        raise ValueError(
            f"unknown translation '{translation}' for book lookup. \n"
            "Try 'bolls -t' to see all available translations, and be sure to use the abbreviation.",
        )
    t = keys[tkey]

    def norm(s: str) -> str:
        return re.sub(r"[^a-z0-9]+", "", s.lower())

    def try_soft_link() -> int | None:
        return _soft_link_book_id(t, book)

    target = norm(book)
    candidates = []
    for entry in data[t]:
        name = entry.get("name", "")
        n = norm(name)
        if n == target:
            return entry.get("bookid")
        if n.startswith(target):
            candidates.append(entry)
    if len(candidates) == 1:
        return candidates[0].get("bookid")
    if len(candidates) > 1:
        soft_id = try_soft_link()
        if soft_id is not None:
            return soft_id
        raise ValueError(f"book name '{book}' is ambiguous for translation '{t}'. Tried soft links.")
    fallback_attempted = False
    if allow_language_fallback:
        try:
            alt_id, fallback_attempted = _book_id_from_language_fallback(t, book, data, norm)
        except ValueError:
            soft_id = try_soft_link()
            if soft_id is not None:
                return soft_id
            raise
        if alt_id is not None:
            return alt_id
    soft_id = try_soft_link()
    if soft_id is not None:
        return soft_id
    suffix_parts = []
    if allow_language_fallback and fallback_attempted:
        suffix_parts.append("Checked other translations in the same language. Tried soft links.")
    suffix = "\n" + " ".join(suffix_parts)
    raise ValueError(
        f"unknown book '{book}' for translation '{t}'.{suffix}\n"
        f"Try 'bolls -b {t}' to find the book you're looking for."
    )

def _normalize_get_verses_json(arg: str) -> str:
    if os.path.isfile(arg):
        with open(arg, "r", encoding="utf-8") as f:
            obj = json.load(f)
    else:
        obj = json.loads(arg)
    if not isinstance(obj, list):
        raise ValueError("get-verses JSON must be an array")
    for entry in obj:
        if not isinstance(entry, dict):
            raise ValueError("get-verses items must be objects")
        if "translation" not in entry or "book" not in entry:
            raise ValueError("get-verses items must include translation and book")
        if isinstance(entry.get("translation"), str):
            entry["translation"] = entry["translation"].upper()
        entry["book"] = _book_to_id(
            entry["translation"],
            entry["book"],
            allow_language_fallback=True,
        )
    return json.dumps(obj)


def _uppercase_translations(translations_json: str) -> str:
    try:
        data = json.loads(translations_json)
    except Exception as exc:
        raise ValueError(f"Invalid translations JSON: {exc}")
    if not isinstance(data, list):
        raise ValueError("Translations must be a JSON array")
    out = [(v.upper() if isinstance(v, str) else v) for v in data]
    return json.dumps(out)


def _first_translation(translations_json: str) -> str:
    try:
        data = json.loads(translations_json)
    except Exception as exc:
        raise ValueError(f"Invalid translations JSON: {exc}")
    if not isinstance(data, list) or not data:
        raise ValueError("Translations list is empty!")
    return data[0]


def _validate_json(body: str) -> None:
    try:
        json.loads(body)
    except Exception as exc:
        raise ValueError(f"Invalid JSON: {exc}")


def _read_file(path: str) -> str:
    with open(path, "r", encoding="utf-8") as f:
        return f.read()


def main(argv: list[str]) -> int:
    raw_json = False
    include_all = False
    add_comments = False
    file_output = False
    url_only = False
    no_api = False

    args = []
    for a in argv:
        if a in ("-j", "--raw-json"):
            raw_json = True
        elif a in ("-a", "--include-all"):
            include_all = True
        elif a in ("-C", "--include-comments"):
            add_comments = True
        elif a in ("-f", "--file"):
            file_output = True
        elif a in ("-u", "--url"):
            url_only = True
        elif a in ("-n", "--no-api"):
            no_api = True
        else:
            args.append(a)

    cmd = args[0] if args else "-h"
    rest = args[1:]

    try:
        if cmd in ("-h", "--help"):
            _print_help()
            return 0
        if cmd in ("-t", "--translations"):
            url = f"{BASE_URL}/static/bolls/app/views/languages.json"
            if url_only:
                _write_output(_format_url("GET", url), False, file_output)
                return 0
            raw = _curl_get(url)
            _write_output(_format_json(raw, raw_json), raw_json, file_output)
            return 0
        if cmd in ("-d", "--dictionaries"):
            url = f"{BASE_URL}/static/bolls/app/views/dictionaries.json"
            if url_only:
                _write_output(_format_url("GET", url), False, file_output)
                return 0
            raw = _curl_get(url)
            _write_output(_format_json(raw, raw_json), raw_json, file_output)
            return 0
        if cmd in ("-b", "--books"):
            if not rest:
                print("Error: Incorrect --books syntax.\nUsage: bolls --books <translation>", file=sys.stderr)
                return 2
            translation = _norm_translation(rest[0])
            url = f"{BASE_URL}/get-books/{translation}/"
            if url_only:
                _write_output(_format_url("GET", url), False, file_output)
                return 0
            raw = _curl_get(url)
            _write_output(_format_json(raw, raw_json), raw_json, file_output)
            return 0

        if cmd in ("-v", "--verses"):
            groups = [g for g in _split_slash_groups(rest) if g]
            output_raw_json = raw_json if not url_only else False

            if groups:
                _enforce_no_api_download_limit(groups, no_api)

            if len(groups) <= 1:
                single_group = groups[0] if groups else rest
                effective_no_api = no_api or _should_default_no_api_for_group(single_group)
                output = _run_verses(single_group, include_all, add_comments, raw_json, url_only, effective_no_api)
                _write_output(output, output_raw_json, file_output)
                return 0

            effective_modes = [no_api or _should_default_no_api_for_group(group) for group in groups]
            if all(not mode for mode in effective_modes):
                combined_body: list[dict] = []
                for group in groups:
                    combined_body.extend(_build_verses_body_objects(group, False))
                output = _run_verses([json.dumps(combined_body)], include_all, add_comments, raw_json, url_only, False)
                _write_output(output, output_raw_json, file_output)
                return 0

            outputs = []
            for group, effective_no_api in zip(groups, effective_modes):
                outputs.append(_run_verses(group, include_all, add_comments, raw_json, url_only, effective_no_api))
            cleaned = [out.rstrip("\n") for out in outputs]
            combined = "\n\n".join(cleaned)
            if outputs and outputs[-1].endswith("\n"):
                combined += "\n"
            _write_output(combined, output_raw_json, file_output)
            return 0

        if cmd in ("-s", "--search"):

            if len(rest) < 2:
                print(
                    "Error: Incorrect --search syntax.\nUsage: bolls --search <translation> [--match-case] [--match-whole] "
                    "[--book <book/ot/nt>] [--page <#>] [--page-limit <#>] <search term>",
                    file=sys.stderr,
                )
                return 2
            translation = _norm_translation(rest[0])
            opts = rest[1:]
            match_case = None
            match_whole = None
            book = None
            page = None
            limit = None
            search_parts = []
            i = 0
            while i < len(opts):
                opt = opts[i]
                if opt == "--":
                    search_parts = opts[i + 1 :]
                    break
                if opt.startswith("-"):
                    if opt in ("--match_case", "--match-case", "-c"):
                        match_case = True
                        i += 1
                        continue
                    if opt in ("--match_whole", "--match-whole", "-w"):
                        match_whole = True
                        i += 1
                        continue
                    if opt in ("--book", "-B"):
                        if i + 1 >= len(opts):
                            raise ValueError("Error: Incorrect --book syntax.\nUsage: bolls --book <book/ot/nt>")
                        book = opts[i + 1]
                        i += 2
                        continue
                    if opt in ("--page", "-p"):
                        if i + 1 >= len(opts):
                            raise ValueError("Error: Incorrect --page syntax.\nUsage: bolls --page <#>")
                        page = opts[i + 1]
                        i += 2
                        continue
                    if opt in ("--limit", "--page-limit", "-l"):
                        if i + 1 >= len(opts):
                            raise ValueError("Error: Incorrect --page-limit syntax.\nUsage: --page-limit <#>")
                        limit = opts[i + 1]
                        i += 2
                        continue
                    raise ValueError(f"Unknown search option: {opt}")
                search_parts = opts[i:]
                break
            if not search_parts:
                raise ValueError("Missing search term")
            piece = " ".join(search_parts).strip()
            if not piece:
                raise ValueError("Missing search term")
            if book:
                if book.lower() in ("ot", "nt"):
                    book = book.lower()
                elif book.isdigit():
                    pass
                else:
                    book = str(_book_to_id(translation, book, allow_language_fallback=True))
            query = f"search={_urlencode(piece)}"
            if match_case is not None:
                query += f"&match_case={_urlencode('true')}"
            if match_whole is not None:
                query += f"&match_whole={_urlencode('true')}"
            if book is not None:
                query += f"&book={_urlencode(book)}"
            if page is not None:
                query += f"&page={_urlencode(page)}"
            if limit is not None:
                query += f"&limit={_urlencode(limit)}"
            url = f"{BASE_URL}/v2/find/{translation}?{query}"
            if url_only:
                _write_output(_format_url("GET", url), False, file_output)
                return 0
            raw = _curl_get(url)
            _write_output(_format_json(raw, raw_json), raw_json, file_output)
            return 0

        if cmd in ("-D", "--define"):
            if len(rest) < 2:
                print("Error: Incorrect --define syntax.\nUsage: bolls --define <dictionary> <Hebrew/Greek word>", file=sys.stderr)
                return 2
            dict_code = rest[0]
            query = " ".join(rest[1:]).strip()
            if not query:
                print("Error: Incorrect --define syntax.\nUsage: bolls --define <dictionary> <Hebrew/Greek word>", file=sys.stderr)
                return 2
            query_enc = _urlencode(query)
            url = f"{BASE_URL}/dictionary-definition/{dict_code}/{query_enc}/"
            if url_only:
                _write_output(_format_url("GET", url), False, file_output)
                return 0
            raw = _curl_get(url)
            _write_output(_format_json(raw, raw_json), raw_json, file_output)
            return 0

        if cmd in ("-r", "--random"):
            if not rest:
                print("Error: Incorrect --random syntax.\nUsage: bolls --random <translation>", file=sys.stderr)
                return 2
            translation = _norm_translation(rest[0])
            url = f"{BASE_URL}/get-random-verse/{translation}/"
            if url_only:
                _write_output(_format_url("GET", url), False, file_output)
                return 0
            raw = _curl_get(url)
            _write_output(_format_json(raw, raw_json), raw_json, file_output)
            return 0

        if cmd.startswith("-"):
            print(f"Unknown flag: {cmd}", file=sys.stderr)
            return 2
        print(f"Unknown subcommand: {cmd}", file=sys.stderr)
        return 2
    except ValueError as exc:
        print(f"Error: {exc}", file=sys.stderr)
        return 2
    except pycurl.error:
        return 2

if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))