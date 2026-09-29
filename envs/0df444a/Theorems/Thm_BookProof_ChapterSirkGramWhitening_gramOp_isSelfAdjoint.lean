-- Prove2me | Theorems.Thm_BookProof_ChapterSirkGramWhitening_gramOp_isSelfAdjoint
-- name    : BookProof.ChapterSirkGramWhitening.gramOp_isSelfAdjoint
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T05:24:35.618885+00:00
-- url     : https://prove2.me/theorems/89fccfbb-31a8-4c60-b088-a59ce3eb8de5
-- title:
--   {m : ℕ} (w : Fin m → E) : IsSelfAdjoint (gramOp w)
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkGramWhitening.gramOp_isSelfAdjoint` (module `BookProof.ChapterSirkGramWhitening`), source chapter `BookProof/ChapterChapterSirkGramWhitening.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkGramWhitening.lean

-- Generated from ChapterSirkGramWhitening.lean — theorem BookProof.ChapterSirkGramWhitening.gramOp_isSelfAdjoint
import Mathlib
import Definitions.Def_ChapterSirkGramWhitening
open BookProof.ChapterSirkGramWhitening








noncomputable section


open scoped InnerProductSpace
open Matrix
open BookProof.ChapterH4 BookProof.ChapterSirkWhitening

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem BookProof.ChapterSirkGramWhitening.gramOp_isSelfAdjoint {m : ℕ} (w : Fin m → E) : IsSelfAdjoint (gramOp w) := by sorry
