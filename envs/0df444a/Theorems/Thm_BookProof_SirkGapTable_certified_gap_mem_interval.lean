-- Prove2me | Theorems.Thm_BookProof_SirkGapTable_certified_gap_mem_interval
-- name    : BookProof.SirkGapTable.certified_gap_mem_interval
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T07:31:59.923711+00:00
-- url     : https://prove2.me/theorems/6ad5a83f-d4e8-476d-aeb6-4ba45b0c829b
-- title:
--   {T P : E →ₗ[ℂ] E} {thetaE thetaO deltaE deltaO : ℝ} (hEvenHi : sectorGround T P 1 ≤ thetaE + deltaE) (hEvenLo : thetaE - deltaE ≤ sectorGround T P 1) (hOddLo : thetaO - deltaO ≤ sectorGround T P...
-- statement:
--   Lean 4 theorem `BookProof.SirkGapTable.certified_gap_mem_interval` (module `BookProof.SirkGapTable`), source chapter `BookProof/ChapterSirkGapTable.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterSirkGapTable.lean

-- Generated from ChapterSirkGapTable.lean — theorem BookProof.SirkGapTable.certified_gap_mem_interval
import Mathlib
import Definitions.Def_ChapterSirkGapTable
open BookProof.SirkGapTable









noncomputable section


open BookProof.SirkCertifiedGap



variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem BookProof.SirkGapTable.certified_gap_mem_interval {T P : E →ₗ[ℂ] E} {thetaE thetaO deltaE deltaO : ℝ}
    (hEvenHi : sectorGround T P 1 ≤ thetaE + deltaE)
    (hEvenLo : thetaE - deltaE ≤ sectorGround T P 1)
    (hOddLo : thetaO - deltaO ≤ sectorGround T P (-1))
    (hOddHi : sectorGround T P (-1) ≤ thetaO + deltaO) :
    sectorGround T P (-1) - sectorGround T P 1 ∈
      Set.Icc (thetaO - thetaE - (deltaO + deltaE)) (thetaO - thetaE + (deltaO + deltaE)) := by sorry
