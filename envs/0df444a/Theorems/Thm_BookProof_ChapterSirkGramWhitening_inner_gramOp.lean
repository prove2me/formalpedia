-- Prove2me | Theorems.Thm_BookProof_ChapterSirkGramWhitening_inner_gramOp
-- name    : BookProof.ChapterSirkGramWhitening.inner_gramOp
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T05:25:11.423682+00:00
-- url     : https://prove2.me/theorems/24e30976-4f1f-4e9d-ada5-469f683ec5a6
-- title:
--   {m : ℕ} (w : Fin m → E) (c d : EuclideanSpace ℂ (Fin m)) : ⟪c, gramOp w d⟫_ℂ = ⟪synthesis w c, synthesis w d⟫_ℂ
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkGramWhitening.inner_gramOp` (module `BookProof.ChapterSirkGramWhitening`), source chapter `BookProof/ChapterChapterSirkGramWhitening.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkGramWhitening.lean

-- Generated from ChapterSirkGramWhitening.lean — theorem BookProof.ChapterSirkGramWhitening.inner_gramOp
import Mathlib
import Definitions.Def_ChapterSirkGramWhitening
open BookProof.ChapterSirkGramWhitening








noncomputable section


open scoped InnerProductSpace
open Matrix
open BookProof.ChapterH4 BookProof.ChapterSirkWhitening

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem BookProof.ChapterSirkGramWhitening.inner_gramOp {m : ℕ} (w : Fin m → E) (c d : EuclideanSpace ℂ (Fin m)) :
    ⟪c, gramOp w d⟫_ℂ = ⟪synthesis w c, synthesis w d⟫_ℂ := by sorry
