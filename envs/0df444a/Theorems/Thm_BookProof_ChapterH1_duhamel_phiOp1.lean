-- Prove2me | Theorems.Thm_BookProof_ChapterH1_duhamel_phiOp1
-- name    : BookProof.ChapterH1.duhamel_phiOp1
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T04:14:41.719107+00:00
-- url     : https://prove2.me/theorems/24fa0080-5dd0-4439-a7dd-4bac9122468c
-- title:
--   {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (g : Fin n → ℂ) (δ : ℝ) : (∫ s in (0 : ℝ)..δ, (NormedSpace.exp ((δ - s) • A)).mulVec g) = δ • phiOp1 (δ • A) g
-- statement:
--   Lean 4 theorem `BookProof.ChapterH1.duhamel_phiOp1` (module `BookProof.ChapterH1`), source chapter `BookProof/ChapterChapterH1.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterH1.lean

-- Generated from ChapterH1.lean — theorem BookProof.ChapterH1.duhamel_phiOp1
import Mathlib
import Definitions.Def_ChapterH1
open BookProof.ChapterH1






open scoped BigOperators
open intervalIntegral


noncomputable section

theorem BookProof.ChapterH1.duhamel_phiOp1 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (g : Fin n → ℂ) (δ : ℝ) :
    (∫ s in (0 : ℝ)..δ, (NormedSpace.exp ((δ - s) • A)).mulVec g)
      = δ • phiOp1 (δ • A) g := by sorry
