-- Prove2me | Theorems.Thm_BookProof_SirkGapTable_gap_le_of_certificate
-- name    : BookProof.SirkGapTable.gap_le_of_certificate
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T07:03:03.729189+00:00
-- url     : https://prove2.me/theorems/4645dfb2-9cfb-47af-8a1c-9dddd1c41635
-- title:
--   {T P : E →ₗ[ℂ] E} {thetaE thetaO deltaE deltaO : ℝ} (hEven : thetaE - deltaE ≤ sectorGround T P 1) (hOdd : sectorGround T P (-1) ≤ thetaO + deltaO) : sectorGround T P (-1) - sectorGround T P 1 ≤...
-- statement:
--   Lean 4 theorem `BookProof.SirkGapTable.gap_le_of_certificate` (module `BookProof.SirkGapTable`), source chapter `BookProof/ChapterSirkGapTable.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterSirkGapTable.lean

-- Generated from ChapterSirkGapTable.lean — theorem BookProof.SirkGapTable.gap_le_of_certificate
import Mathlib
import Definitions.Def_ChapterSirkGapTable
open BookProof.SirkGapTable









noncomputable section


open BookProof.SirkCertifiedGap



variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem BookProof.SirkGapTable.gap_le_of_certificate {T P : E →ₗ[ℂ] E} {thetaE thetaO deltaE deltaO : ℝ}
    (hEven : thetaE - deltaE ≤ sectorGround T P 1)
    (hOdd : sectorGround T P (-1) ≤ thetaO + deltaO) :
    sectorGround T P (-1) - sectorGround T P 1 ≤ thetaO - thetaE + (deltaO + deltaE) := by sorry
