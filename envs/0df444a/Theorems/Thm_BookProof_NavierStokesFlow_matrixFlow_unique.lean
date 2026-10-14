-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_matrixFlow_unique
-- name    : BookProof.NavierStokesFlow.matrixFlow_unique
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-11T19:16:01.270133+00:00
-- url     : https://prove2.me/theorems/4bf381fb-e96f-4388-8e09-f565e613d6b3
-- title:
--   `BookProof.NavierStokesFlow.matrixFlow_unique` (A : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ) (y : ℝ → Fin n → ℂ) (hy : ∀ t, HasDerivAt y (A *ᵥ y t) t) (hy0 : y 0 = x) (t : ℝ) : y
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesCauchy`.
--
--   `BookProof.NavierStokesFlow.matrixFlow_unique` (A : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ) (y : ℝ → Fin n → ℂ) (hy : ∀ t, HasDerivAt y (A *ᵥ y t) t) (hy0 : y 0 = x) (t : ℝ) : y t = matrixFlow A t *ᵥ x
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.matrixFlow_unique`.

-- Generated from ChapterNavierStokesCauchy.lean — theorem BookProof.NavierStokesFlow.matrixFlow_unique
import Mathlib
import Definitions.Def_ChapterNavierStokesCauchy
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow


open scoped BigOperators Matrix Matrix.Norms.Operator

variable {n : ℕ}

theorem BookProof.NavierStokesFlow.matrixFlow_unique (A : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ) (y : ℝ → Fin n → ℂ)
    (hy : ∀ t, HasDerivAt y (A *ᵥ y t) t) (hy0 : y 0 = x) (t : ℝ) :
    y t = matrixFlow A t *ᵥ x := by sorry
