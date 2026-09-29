-- Prove2me | Theorems.Thm_BookProof_ChapterSirkGramWhitening_gramOp_apply
-- name    : BookProof.ChapterSirkGramWhitening.gramOp_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T05:54:47.377879+00:00
-- url     : https://prove2.me/theorems/d8caa162-e546-423d-93dd-684aa981aa88
-- title:
--   {m : ℕ} (w : Fin m → E) (c : EuclideanSpace ℂ (Fin m)) (i : Fin m) : gramOp w c i = ∑ j, ⟪w i, w j⟫_ℂ * c j
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkGramWhitening.gramOp_apply` (module `BookProof.ChapterSirkGramWhitening`), source chapter `BookProof/ChapterChapterSirkGramWhitening.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkGramWhitening.lean

-- Generated from ChapterSirkGramWhitening.lean — theorem BookProof.ChapterSirkGramWhitening.gramOp_apply
import Mathlib
import Definitions.Def_ChapterSirkGramWhitening
open BookProof.ChapterSirkGramWhitening








noncomputable section


open scoped InnerProductSpace
open Matrix
open BookProof.ChapterH4 BookProof.ChapterSirkWhitening

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem BookProof.ChapterSirkGramWhitening.gramOp_apply {m : ℕ} (w : Fin m → E) (c : EuclideanSpace ℂ (Fin m)) (i : Fin m) :
    gramOp w c i = ∑ j, ⟪w i, w j⟫_ℂ * c j := by sorry
