-- Prove2me | Theorems.Thm_BookProof_ChapterH7_generationOperator_conjTranspose
-- name    : BookProof.ChapterH7.generationOperator_conjTranspose
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-05T19:45:28.466914+00:00
-- url     : https://prove2.me/theorems/a034bba7-7686-420e-a750-adf4bc996584
-- title:
--   `BookProof.ChapterH7.generationOperator_conjTranspose` (A : Matrix (Fin m) (Fin m) ℂ) (t : ℝ) (hA : A.IsHermitian) : (generationOperator A t)ᴴ = NormedSpace.exp ((Complex.I * (t :
-- statement:
--   Prove the following Lean 4 theorem from `ChapterH7`.
--
--   `BookProof.ChapterH7.generationOperator_conjTranspose` (A : Matrix (Fin m) (Fin m) ℂ) (t : ℝ) (hA : A.IsHermitian) : (generationOperator A t)ᴴ = NormedSpace.exp ((Complex.I * (t : ℂ)) • A)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterH7.generationOperator_conjTranspose`.

-- Generated from ChapterH7.lean — theorem BookProof.ChapterH7.generationOperator_conjTranspose
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

theorem BookProof.ChapterH7.generationOperator_conjTranspose (A : Matrix (Fin m) (Fin m) ℂ) (t : ℝ)
    (hA : A.IsHermitian) :
    (generationOperator A t)ᴴ = NormedSpace.exp ((Complex.I * (t : ℂ)) • A) := by sorry
