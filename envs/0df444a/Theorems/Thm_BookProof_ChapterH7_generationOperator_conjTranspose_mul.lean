-- Prove2me | Theorems.Thm_BookProof_ChapterH7_generationOperator_conjTranspose_mul
-- name    : BookProof.ChapterH7.generationOperator_conjTranspose_mul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-04T19:55:39.061459+00:00
-- url     : https://prove2.me/theorems/361ffd39-ac67-4c01-b1eb-9c6629f4d2d4
-- title:
--   `BookProof.ChapterH7.generationOperator_conjTranspose_mul` (A : Matrix (Fin m) (Fin m) ℂ) (t : ℝ) (hA : A.IsHermitian) : (generationOperator A t)ᴴ * generationOperator A t = 1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterH7`.
--
--   `BookProof.ChapterH7.generationOperator_conjTranspose_mul` (A : Matrix (Fin m) (Fin m) ℂ) (t : ℝ) (hA : A.IsHermitian) : (generationOperator A t)ᴴ * generationOperator A t = 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterH7.generationOperator_conjTranspose_mul`.

-- Generated from ChapterH7.lean — theorem BookProof.ChapterH7.generationOperator_conjTranspose_mul
import Definitions.Def_ChapterH4
import Definitions.Def_ChapterH6
import Mathlib
import Definitions.Def_ChapterH7
import Definitions.Def_ChapterShiftedQuadraticEsa
open BookProof.ChapterH7


noncomputable section

open BookProof.ChapterH4 BookProof.ChapterH6
open scoped Matrix

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {m : ℕ}

theorem BookProof.ChapterH7.generationOperator_conjTranspose_mul (A : Matrix (Fin m) (Fin m) ℂ) (t : ℝ)
    (hA : A.IsHermitian) :
    (generationOperator A t)ᴴ * generationOperator A t = 1 := by sorry
