-- Prove2me | Theorems.Thm_BookProof_ChapterSirkGramWhitening_whitened_apply
-- name    : BookProof.ChapterSirkGramWhitening.whitened_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T05:31:10.492124+00:00
-- url     : https://prove2.me/theorems/9c8f7fab-0c65-4a7c-80c1-c071f3d231a2
-- title:
--   {m : ℕ} (w : Fin m → E) (T : EuclideanSpace ℂ (Fin m) →L[ℂ] EuclideanSpace ℂ (Fin m)) (c : EuclideanSpace ℂ (Fin m)) : whitened w T c = synthesis w (T c)
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkGramWhitening.whitened_apply` (module `BookProof.ChapterSirkGramWhitening`), source chapter `BookProof/ChapterChapterSirkGramWhitening.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkGramWhitening.lean

-- Generated from ChapterSirkGramWhitening.lean — theorem BookProof.ChapterSirkGramWhitening.whitened_apply
import Mathlib
import Definitions.Def_ChapterSirkGramWhitening
open BookProof.ChapterSirkGramWhitening








noncomputable section


open scoped InnerProductSpace
open Matrix
open BookProof.ChapterH4 BookProof.ChapterSirkWhitening

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem BookProof.ChapterSirkGramWhitening.whitened_apply {m : ℕ} (w : Fin m → E)
    (T : EuclideanSpace ℂ (Fin m) →L[ℂ] EuclideanSpace ℂ (Fin m))
    (c : EuclideanSpace ℂ (Fin m)) : whitened w T c = synthesis w (T c) := by sorry
