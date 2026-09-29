-- Prove2me | Theorems.Thm_BookProof_SirkGapTable_certified_gap_table_interval
-- name    : BookProof.SirkGapTable.certified_gap_table_interval
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T07:35:44.416104+00:00
-- url     : https://prove2.me/theorems/5abc8faa-d90f-4b7e-9c3e-286caa3519e1
-- title:
--   {n : ℕ} (row : Fin n → CouplingCertificate) (T P : Fin n → E →ₗ[ℂ] E) (thetaE thetaO deltaE deltaO : Fin n → ℝ) (hgap : ∀ i, (row i).gap = thetaO i - thetaE i) (hwidth : ∀ i, (row i).width =...
-- statement:
--   Lean 4 theorem `BookProof.SirkGapTable.certified_gap_table_interval` (module `BookProof.SirkGapTable`), source chapter `BookProof/ChapterSirkGapTable.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterSirkGapTable.lean

-- Generated from ChapterSirkGapTable.lean — theorem BookProof.SirkGapTable.certified_gap_table_interval
import Mathlib
import Definitions.Def_ChapterSirkGapTable
open BookProof.SirkGapTable









noncomputable section


open BookProof.SirkCertifiedGap



variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]










variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem BookProof.SirkGapTable.certified_gap_table_interval {n : ℕ} (row : Fin n → CouplingCertificate)
    (T P : Fin n → E →ₗ[ℂ] E) (thetaE thetaO deltaE deltaO : Fin n → ℝ)
    (hgap : ∀ i, (row i).gap = thetaO i - thetaE i)
    (hwidth : ∀ i, (row i).width = deltaO i + deltaE i)
    (hEvenHi : ∀ i, sectorGround (T i) (P i) 1 ≤ thetaE i + deltaE i)
    (hEvenLo : ∀ i, thetaE i - deltaE i ≤ sectorGround (T i) (P i) 1)
    (hOddLo : ∀ i, thetaO i - deltaO i ≤ sectorGround (T i) (P i) (-1))
    (hOddHi : ∀ i, sectorGround (T i) (P i) (-1) ≤ thetaO i + deltaO i) :
    ∀ i, sectorGround (T i) (P i) (-1) - sectorGround (T i) (P i) 1
        ∈ Set.Icc (row i).lo (row i).hi := by sorry
