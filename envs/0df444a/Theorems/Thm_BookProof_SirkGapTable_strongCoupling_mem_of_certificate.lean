-- Prove2me | Theorems.Thm_BookProof_SirkGapTable_strongCoupling_mem_of_certificate
-- name    : BookProof.SirkGapTable.strongCoupling_mem_of_certificate
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T07:03:31.965056+00:00
-- url     : https://prove2.me/theorems/703d0647-fd01-4cd4-8c9f-298dff389e55
-- title:
--   {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {T P : E →ₗ[ℂ] E} (c : CouplingCertificate) {thetaE thetaO deltaE deltaO : ℝ} (hgap : c.gap = thetaO - thetaE) (hwidth : c.width =...
-- statement:
--   Lean 4 theorem `BookProof.SirkGapTable.strongCoupling_mem_of_certificate` (module `BookProof.SirkGapTable`), source chapter `BookProof/ChapterSirkGapTable.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterSirkGapTable.lean

-- Generated from ChapterSirkGapTable.lean — theorem BookProof.SirkGapTable.strongCoupling_mem_of_certificate
import Mathlib
import Definitions.Def_ChapterSirkGapTable
open BookProof.SirkGapTable









noncomputable section


open BookProof.SirkCertifiedGap



variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]










variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem BookProof.SirkGapTable.strongCoupling_mem_of_certificate {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {T P : E →ₗ[ℂ] E} (c : CouplingCertificate)
    {thetaE thetaO deltaE deltaO : ℝ}
    (hgap : c.gap = thetaO - thetaE) (hwidth : c.width = deltaO + deltaE)
    (hEven : sectorGround T P 1 ≤ thetaE + deltaE)
    (hOdd : thetaO - deltaO ≤ sectorGround T P (-1))
    (hcons : c.strongCouplingConsistent) :
    c.lo ≤ sectorGround T P (-1) - sectorGround T P 1 ∧ c.lo ≤ strongCoupling c.g := by sorry
