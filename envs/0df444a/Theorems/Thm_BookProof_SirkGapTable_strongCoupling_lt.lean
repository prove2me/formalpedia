-- Prove2me | Theorems.Thm_BookProof_SirkGapTable_strongCoupling_lt
-- name    : BookProof.SirkGapTable.strongCoupling_lt
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T09:46:27.208843+00:00
-- url     : https://prove2.me/theorems/170744d4-532d-433d-984a-19280af1b330
-- title:
--   {g₁ g₂ : ℝ} (h0 : 0 ≤ g₁) (h : g₁ < g₂) : strongCoupling g₁ < strongCoupling g₂
-- statement:
--   Lean 4 theorem `BookProof.SirkGapTable.strongCoupling_lt` (module `BookProof.SirkGapTable`), source chapter `BookProof/ChapterSirkGapTable.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterSirkGapTable.lean

-- Generated from ChapterSirkGapTable.lean — theorem BookProof.SirkGapTable.strongCoupling_lt
import Mathlib
import Definitions.Def_ChapterSirkGapTable
open BookProof.SirkGapTable









noncomputable section


open BookProof.SirkCertifiedGap



variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]










variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem BookProof.SirkGapTable.strongCoupling_lt {g₁ g₂ : ℝ} (h0 : 0 ≤ g₁) (h : g₁ < g₂) :
    strongCoupling g₁ < strongCoupling g₂ := by sorry
