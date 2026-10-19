-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_matrixFlow_cauchy_existsUnique
-- name    : BookProof.NavierStokesFlow.matrixFlow_cauchy_existsUnique
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T19:16:22.796136+00:00
-- url     : https://prove2.me/theorems/889ff4dc-48d4-4c98-8cc9-799b743032dc
-- title:
--   `BookProof.NavierStokesFlow.matrixFlow_cauchy_existsUnique` (A : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ) : ∃! y : ℝ → Fin n → ℂ, y 0 = x ∧ ∀ t, HasDerivAt y (A *ᵥ y t) t
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesCauchy`.
--
--   `BookProof.NavierStokesFlow.matrixFlow_cauchy_existsUnique` (A : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ) : ∃! y : ℝ → Fin n → ℂ, y 0 = x ∧ ∀ t, HasDerivAt y (A *ᵥ y t) t
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.matrixFlow_cauchy_existsUnique`.

-- Generated from ChapterNavierStokesCauchy.lean — theorem BookProof.NavierStokesFlow.matrixFlow_cauchy_existsUnique
import Mathlib
import Definitions.Def_ChapterNavierStokesCauchy
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow


open scoped BigOperators Matrix Matrix.Norms.Operator

variable {n : ℕ}

theorem BookProof.NavierStokesFlow.matrixFlow_cauchy_existsUnique (A : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ) :
    ∃! y : ℝ → Fin n → ℂ, y 0 = x ∧ ∀ t, HasDerivAt y (A *ᵥ y t) t := by sorry
