-- Prove2me | Theorems.Thm_BookProof_SirkCertificateReader_parseDec_reject
-- name    : BookProof.SirkCertificateReader.parseDec_reject
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T12:49:45.620381+00:00
-- url     : https://prove2.me/theorems/972e2635-cd0f-44e3-9993-a177e0bfc988
-- title:
--   : parseDec "NaN".toList = none
-- statement:
--   Lean 4 theorem `BookProof.SirkCertificateReader.parseDec_reject` (module `BookProof.SirkCertificateReader`), source chapter `BookProof/ChapterSirkCertificateReader.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterSirkCertificateReader.lean

-- Generated from ChapterSirkCertificateReader.lean — theorem BookProof.SirkCertificateReader.parseDec_reject
import Mathlib
import Definitions.Def_ChapterSirkCertificateReader
open BookProof.SirkCertificateReader









open BookProof.SirkCertifiedGap

theorem BookProof.SirkCertificateReader.parseDec_reject : parseDec "NaN".toList = none := by sorry
