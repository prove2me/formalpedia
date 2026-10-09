-- Prove2me | Theorems.Thm_BookProof_ChapterH7_generation_preserves_l2
-- name    : BookProof.ChapterH7.generation_preserves_l2
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T11:54:28.879985+00:00
-- url     : https://prove2.me/theorems/eadf6124-5295-45be-a394-ce6a034914b1
-- title:
--   `BookProof.ChapterH7.generation_preserves_l2` (A : Matrix (Fin m) (Fin m) ℂ) (t : ℝ) (hA : A.IsHermitian) (psi0 : Fin m → ℂ) : ∑ i, Complex.normSq (generatedState A (t : ℂ) psi0 i)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterH7`.
--
--   `BookProof.ChapterH7.generation_preserves_l2` (A : Matrix (Fin m) (Fin m) ℂ) (t : ℝ) (hA : A.IsHermitian) (psi0 : Fin m → ℂ) : ∑ i, Complex.normSq (generatedState A (t : ℂ) psi0 i) = ∑ i, Complex.normSq (psi0 i)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterH7.generation_preserves_l2`.

-- Generated from ChapterH7.lean — theorem BookProof.ChapterH7.generation_preserves_l2
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

theorem BookProof.ChapterH7.generation_preserves_l2 (A : Matrix (Fin m) (Fin m) ℂ) (t : ℝ)
    (hA : A.IsHermitian) (psi0 : Fin m → ℂ) :
    ∑ i, Complex.normSq (generatedState A (t : ℂ) psi0 i) = ∑ i, Complex.normSq (psi0 i) := by sorry
