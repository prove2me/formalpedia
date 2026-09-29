-- Prove2me | Theorems.Thm_BookProof_SirkCertificateReader_gap_pos_of_ndjson
-- name    : BookProof.SirkCertificateReader.gap_pos_of_ndjson
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T07:57:59.199588+00:00
-- url     : https://prove2.me/theorems/2b3f6861-a3dd-47ed-822d-9a99979f976d
-- title:
--   {T P : E →ₗ[ℂ] E} {s : String} {d : CertificateData} {lo : ℚ} (hd : parseCertificate s = some d) (hs : ndjsonLower s = some lo) (hpos : 0 < lo) (hEven : sectorGround T P 1 ≤...
-- statement:
--   Lean 4 theorem `BookProof.SirkCertificateReader.gap_pos_of_ndjson` (module `BookProof.SirkCertificateReader`), source chapter `BookProof/ChapterSirkCertificateReader.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterSirkCertificateReader.lean

-- Generated from ChapterSirkCertificateReader.lean — theorem BookProof.SirkCertificateReader.gap_pos_of_ndjson
import Mathlib
import Definitions.Def_ChapterSirkCertificateReader
open BookProof.SirkCertificateReader









open BookProof.SirkCertifiedGap




































variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem BookProof.SirkCertificateReader.gap_pos_of_ndjson {T P : E →ₗ[ℂ] E} {s : String} {d : CertificateData} {lo : ℚ}
    (hd : parseCertificate s = some d) (hs : ndjsonLower s = some lo) (hpos : 0 < lo)
    (hEven : sectorGround T P 1 ≤ ((d.even.theta.toQ : ℚ) : ℝ) + ((d.even.delta.toQ : ℚ) : ℝ))
    (hOdd : ((d.odd.theta.toQ : ℚ) : ℝ) - ((d.odd.delta.toQ : ℚ) : ℝ) ≤ sectorGround T P (-1)) :
    sectorGround T P 1 < sectorGround T P (-1) := by sorry
