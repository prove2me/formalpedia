-- Prove2me | Theorems.Thm_BookProof_ChapterSirkGramWhitening_synthesis_apply
-- name    : BookProof.ChapterSirkGramWhitening.synthesis_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T05:29:44.038909+00:00
-- url     : https://prove2.me/theorems/c6a5ace1-3835-42ee-91f2-45c8acaed8c1
-- title:
--   {m : ℕ} (w : Fin m → E) (c : EuclideanSpace ℂ (Fin m)) : synthesis w c = ∑ i, c i • w i
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkGramWhitening.synthesis_apply` (module `BookProof.ChapterSirkGramWhitening`), source chapter `BookProof/ChapterChapterSirkGramWhitening.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkGramWhitening.lean

-- Generated from ChapterSirkGramWhitening.lean — theorem BookProof.ChapterSirkGramWhitening.synthesis_apply
import Mathlib
import Definitions.Def_ChapterSirkGramWhitening
open BookProof.ChapterSirkGramWhitening








noncomputable section


open scoped InnerProductSpace
open Matrix
open BookProof.ChapterH4 BookProof.ChapterSirkWhitening

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem BookProof.ChapterSirkGramWhitening.synthesis_apply {m : ℕ} (w : Fin m → E) (c : EuclideanSpace ℂ (Fin m)) :
    synthesis w c = ∑ i, c i • w i := by sorry
