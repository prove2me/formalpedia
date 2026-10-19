-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_nsFlow_unique_solution
-- name    : BookProof.NavierStokesFlow.nsFlow_unique_solution
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T19:16:20.339316+00:00
-- url     : https://prove2.me/theorems/27613955-075e-4cd8-b745-312f9590a302
-- title:
--   `BookProof.NavierStokesFlow.nsFlow_unique_solution` (psi : Fin n → ℂ) (y : ℝ → Fin n → ℂ) (hy : ∀ t, HasDerivAt y ((Complex.I • nsHamiltonian d) *ᵥ y t) t) (hy0 : y 0 = psi) (t : ℝ
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesCauchy`.
--
--   `BookProof.NavierStokesFlow.nsFlow_unique_solution` (psi : Fin n → ℂ) (y : ℝ → Fin n → ℂ) (hy : ∀ t, HasDerivAt y ((Complex.I • nsHamiltonian d) *ᵥ y t) t) (hy0 : y 0 = psi) (t : ℝ) : y t = nsFlowUnitary d t *ᵥ psi
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.nsFlow_unique_solution`.

-- Generated from ChapterNavierStokesCauchy.lean — theorem BookProof.NavierStokesFlow.nsFlow_unique_solution
import Mathlib
import Definitions.Def_ChapterNavierStokesCauchy
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow


open scoped BigOperators Matrix Matrix.Norms.Operator

variable {n : ℕ}
variable {n : ℕ} (d : NSTruncation n)

theorem BookProof.NavierStokesFlow.nsFlow_unique_solution (psi : Fin n → ℂ) (y : ℝ → Fin n → ℂ)
    (hy : ∀ t, HasDerivAt y ((Complex.I • nsHamiltonian d) *ᵥ y t) t) (hy0 : y 0 = psi)
    (t : ℝ) : y t = nsFlowUnitary d t *ᵥ psi := by sorry
