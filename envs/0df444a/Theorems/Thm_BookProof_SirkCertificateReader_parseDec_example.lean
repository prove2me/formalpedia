-- Prove2me | Theorems.Thm_BookProof_SirkCertificateReader_parseDec_example
-- name    : BookProof.SirkCertificateReader.parseDec_example
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T12:12:50.158157+00:00
-- url     : https://prove2.me/theorems/924b0c1f-006c-405a-8da6-f0002ee94dd7
-- title:
--   : parseDec "1.9875".toList = some ⟨19875, 4⟩
-- statement:
--   Lean 4 theorem `BookProof.SirkCertificateReader.parseDec_example` (module `BookProof.SirkCertificateReader`), source chapter `BookProof/ChapterSirkCertificateReader.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterSirkCertificateReader.lean

-- Generated from ChapterSirkCertificateReader.lean — theorem BookProof.SirkCertificateReader.parseDec_example
import Mathlib
import Definitions.Def_ChapterSirkCertificateReader
open BookProof.SirkCertificateReader









open BookProof.SirkCertifiedGap

theorem BookProof.SirkCertificateReader.parseDec_example : parseDec "1.9875".toList = some ⟨19875, 4⟩ := by sorry
