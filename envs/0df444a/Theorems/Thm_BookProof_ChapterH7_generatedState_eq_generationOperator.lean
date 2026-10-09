-- Prove2me | Theorems.Thm_BookProof_ChapterH7_generatedState_eq_generationOperator
-- name    : BookProof.ChapterH7.generatedState_eq_generationOperator
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T11:54:17.8102+00:00
-- url     : https://prove2.me/theorems/f0c62b7b-835f-43c7-b44d-6bafb3489058
-- title:
--   `BookProof.ChapterH7.generatedState_eq_generationOperator` (A : Matrix (Fin m) (Fin m) ℂ) (t : ℝ) (psi0 : Fin m → ℂ) : generatedState A (t : ℂ) psi0 = (generationOperator A t).mulV
-- statement:
--   Prove the following Lean 4 theorem from `ChapterH7`.
--
--   `BookProof.ChapterH7.generatedState_eq_generationOperator` (A : Matrix (Fin m) (Fin m) ℂ) (t : ℝ) (psi0 : Fin m → ℂ) : generatedState A (t : ℂ) psi0 = (generationOperator A t).mulVec psi0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterH7.generatedState_eq_generationOperator`.

-- Generated from ChapterH7.lean — theorem BookProof.ChapterH7.generatedState_eq_generationOperator
import Definitions.Def_ChapterH4
import Mathlib
import Definitions.Def_ChapterH7
import Definitions.Def_ChapterH6
open BookProof.ChapterH6
open BookProof.ChapterH7


noncomputable section

open BookProof.ChapterH4 BookProof.ChapterH6

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {m : ℕ}

theorem BookProof.ChapterH7.generatedState_eq_generationOperator (A : Matrix (Fin m) (Fin m) ℂ) (t : ℝ)
    (psi0 : Fin m → ℂ) :
    generatedState A (t : ℂ) psi0 = (generationOperator A t).mulVec psi0 := by sorry
