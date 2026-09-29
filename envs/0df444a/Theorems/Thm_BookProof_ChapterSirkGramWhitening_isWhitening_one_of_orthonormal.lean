-- Prove2me | Theorems.Thm_BookProof_ChapterSirkGramWhitening_isWhitening_one_of_orthonormal
-- name    : BookProof.ChapterSirkGramWhitening.isWhitening_one_of_orthonormal
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T06:02:25.890122+00:00
-- url     : https://prove2.me/theorems/e1750671-beab-4c41-9685-9d826b8ca36b
-- title:
--   {m : ℕ} {w : Fin m → E} (hw : Orthonormal ℂ w) : IsWhitening w (Matrix.toEuclideanCLM (𝕜
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkGramWhitening.isWhitening_one_of_orthonormal` (module `BookProof.ChapterSirkGramWhitening`), source chapter `BookProof/ChapterChapterSirkGramWhitening.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkGramWhitening.lean

-- Generated from ChapterSirkGramWhitening.lean — theorem BookProof.ChapterSirkGramWhitening.isWhitening_one_of_orthonormal
import Mathlib
import Definitions.Def_ChapterSirkGramWhitening
open BookProof.ChapterSirkGramWhitening








noncomputable section


open scoped InnerProductSpace
open Matrix
open BookProof.ChapterH4 BookProof.ChapterSirkWhitening

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem BookProof.ChapterSirkGramWhitening.isWhitening_one_of_orthonormal {m : ℕ} {w : Fin m → E} (hw : Orthonormal ℂ w) :
    IsWhitening w (Matrix.toEuclideanCLM (𝕜 := ℂ) (1 : Matrix (Fin m) (Fin m) ℂ)) := by sorry
