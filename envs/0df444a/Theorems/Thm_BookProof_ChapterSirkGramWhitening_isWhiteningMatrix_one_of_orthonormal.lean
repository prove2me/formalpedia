-- Prove2me | Theorems.Thm_BookProof_ChapterSirkGramWhitening_isWhiteningMatrix_one_of_orthonormal
-- name    : BookProof.ChapterSirkGramWhitening.isWhiteningMatrix_one_of_orthonormal
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T05:26:35.310102+00:00
-- url     : https://prove2.me/theorems/243ef798-c108-4df5-b84d-7f8d7cb9019a
-- title:
--   {m : ℕ} {w : Fin m → E} (hw : Orthonormal ℂ w) : IsWhiteningMatrix w 1
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkGramWhitening.isWhiteningMatrix_one_of_orthonormal` (module `BookProof.ChapterSirkGramWhitening`), source chapter `BookProof/ChapterChapterSirkGramWhitening.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkGramWhitening.lean

-- Generated from ChapterSirkGramWhitening.lean — theorem BookProof.ChapterSirkGramWhitening.isWhiteningMatrix_one_of_orthonormal
import Mathlib
import Definitions.Def_ChapterSirkGramWhitening
open BookProof.ChapterSirkGramWhitening








noncomputable section


open scoped InnerProductSpace
open Matrix
open BookProof.ChapterH4 BookProof.ChapterSirkWhitening

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem BookProof.ChapterSirkGramWhitening.isWhiteningMatrix_one_of_orthonormal {m : ℕ} {w : Fin m → E}
    (hw : Orthonormal ℂ w) : IsWhiteningMatrix w 1 := by sorry
