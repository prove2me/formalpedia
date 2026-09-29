-- Prove2me | Theorems.Thm_BookProof_SirkGapTable_certified_gap_table
-- name    : BookProof.SirkGapTable.certified_gap_table
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T07:02:25.315492+00:00
-- url     : https://prove2.me/theorems/55fc216c-d18f-49dc-b830-43af2827e958
-- title:
--   {n : ℕ} (row : Fin n → CouplingCertificate) (T P : Fin n → E →ₗ[ℂ] E) (thetaE thetaO deltaE deltaO : Fin n → ℝ) (hgap : ∀ i, (row i).gap = thetaO i - thetaE i) (hwidth : ∀ i, (row i).width =...
-- statement:
--   Lean 4 theorem `BookProof.SirkGapTable.certified_gap_table` (module `BookProof.SirkGapTable`), source chapter `BookProof/ChapterSirkGapTable.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterSirkGapTable.lean

-- Generated from ChapterSirkGapTable.lean — theorem BookProof.SirkGapTable.certified_gap_table
import Mathlib
import Definitions.Def_ChapterSirkGapTable
open BookProof.SirkGapTable









noncomputable section


open BookProof.SirkCertifiedGap



variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]










variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem BookProof.SirkGapTable.certified_gap_table {n : ℕ} (row : Fin n → CouplingCertificate)
    (T P : Fin n → E →ₗ[ℂ] E) (thetaE thetaO deltaE deltaO : Fin n → ℝ)
    (hgap : ∀ i, (row i).gap = thetaO i - thetaE i)
    (hwidth : ∀ i, (row i).width = deltaO i + deltaE i)
    (hEven : ∀ i, sectorGround (T i) (P i) 1 ≤ thetaE i + deltaE i)
    (hOdd : ∀ i, thetaO i - deltaO i ≤ sectorGround (T i) (P i) (-1)) :
    ∀ i, (row i).lo ≤ sectorGround (T i) (P i) (-1) - sectorGround (T i) (P i) 1 := by sorry
