-- Prove2me | Theorems.Thm_BookProof_ChapterSirkGramWhitening_isWhitening_of_matrix
-- name    : BookProof.ChapterSirkGramWhitening.isWhitening_of_matrix
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T06:00:11.134563+00:00
-- url     : https://prove2.me/theorems/6890eb57-8e09-42c9-a64a-2a47d3320e61
-- title:
--   {m : ℕ} (w : Fin m → E) {M : Matrix (Fin m) (Fin m) ℂ} (hM : IsWhiteningMatrix w M) : IsWhitening w (Matrix.toEuclideanCLM (𝕜
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkGramWhitening.isWhitening_of_matrix` (module `BookProof.ChapterSirkGramWhitening`), source chapter `BookProof/ChapterChapterSirkGramWhitening.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkGramWhitening.lean

-- Generated from ChapterSirkGramWhitening.lean — theorem BookProof.ChapterSirkGramWhitening.isWhitening_of_matrix
import Mathlib
import Definitions.Def_ChapterSirkGramWhitening
open BookProof.ChapterSirkGramWhitening








noncomputable section


open scoped InnerProductSpace
open Matrix
open BookProof.ChapterH4 BookProof.ChapterSirkWhitening

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem BookProof.ChapterSirkGramWhitening.isWhitening_of_matrix {m : ℕ} (w : Fin m → E) {M : Matrix (Fin m) (Fin m) ℂ}
    (hM : IsWhiteningMatrix w M) :
    IsWhitening w (Matrix.toEuclideanCLM (𝕜 := ℂ) M) := by sorry
