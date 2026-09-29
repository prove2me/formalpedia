-- Prove2me | Theorems.Thm_BookProof_ChapterSirkGramWhitening_gramOp_nonneg
-- name    : BookProof.ChapterSirkGramWhitening.gramOp_nonneg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T05:44:17.499534+00:00
-- url     : https://prove2.me/theorems/08f16939-a22b-4e35-86c7-4ecb8e08dd63
-- title:
--   {m : ℕ} (w : Fin m → E) (c : EuclideanSpace ℂ (Fin m)) : 0 ≤ (⟪c, gramOp w c⟫_ℂ).re
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkGramWhitening.gramOp_nonneg` (module `BookProof.ChapterSirkGramWhitening`), source chapter `BookProof/ChapterChapterSirkGramWhitening.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkGramWhitening.lean

-- Generated from ChapterSirkGramWhitening.lean — theorem BookProof.ChapterSirkGramWhitening.gramOp_nonneg
import Mathlib
import Definitions.Def_ChapterSirkGramWhitening
open BookProof.ChapterSirkGramWhitening








noncomputable section


open scoped InnerProductSpace
open Matrix
open BookProof.ChapterH4 BookProof.ChapterSirkWhitening

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem BookProof.ChapterSirkGramWhitening.gramOp_nonneg {m : ℕ} (w : Fin m → E) (c : EuclideanSpace ℂ (Fin m)) :
    0 ≤ (⟪c, gramOp w c⟫_ℂ).re := by sorry
