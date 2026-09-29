-- Prove2me | Theorems.Thm_BookProof_SirkCertificateReader_formatExample_lower
-- name    : BookProof.SirkCertificateReader.formatExample_lower
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T13:52:56.64992+00:00
-- url     : https://prove2.me/theorems/c07bd00a-abc4-41c4-bbd6-5adcfc7f164d
-- title:
--   : ndjsonLower formatExampleNdjson = some (1932 / 1000)
-- statement:
--   Lean 4 theorem `BookProof.SirkCertificateReader.formatExample_lower` (module `BookProof.SirkCertificateReader`), source chapter `BookProof/ChapterSirkCertificateReader.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterSirkCertificateReader.lean

-- Generated from ChapterSirkCertificateReader.lean — theorem BookProof.SirkCertificateReader.formatExample_lower
import Mathlib
import Definitions.Def_ChapterSirkCertificateReader
open BookProof.SirkCertificateReader









open BookProof.SirkCertifiedGap




































variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem BookProof.SirkCertificateReader.formatExample_lower : ndjsonLower formatExampleNdjson = some (1932 / 1000) := by sorry
