-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_nsFlow_solves_schrodinger
-- name    : BookProof.NavierStokesFlow.nsFlow_solves_schrodinger
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T19:16:09.50737+00:00
-- url     : https://prove2.me/theorems/4d45d47d-e604-4a27-8e97-f22d7c109faa
-- title:
--   `BookProof.NavierStokesFlow.nsFlow_solves_schrodinger` (psi : Fin n → ℂ) (t : ℝ) : HasDerivAt (fun s : ℝ => nsFlowUnitary d s *ᵥ psi) ((Complex.I • nsHamiltonian d) *ᵥ (nsFlowUnita
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesCauchy`.
--
--   `BookProof.NavierStokesFlow.nsFlow_solves_schrodinger` (psi : Fin n → ℂ) (t : ℝ) : HasDerivAt (fun s : ℝ => nsFlowUnitary d s *ᵥ psi) ((Complex.I • nsHamiltonian d) *ᵥ (nsFlowUnitary d t *ᵥ psi)) t
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.nsFlow_solves_schrodinger`.

-- Generated from ChapterNavierStokesCauchy.lean — theorem BookProof.NavierStokesFlow.nsFlow_solves_schrodinger
import Mathlib
import Definitions.Def_ChapterNavierStokesCauchy
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow


open scoped BigOperators Matrix Matrix.Norms.Operator

variable {n : ℕ}
variable {n : ℕ} (d : NSTruncation n)

theorem BookProof.NavierStokesFlow.nsFlow_solves_schrodinger (psi : Fin n → ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => nsFlowUnitary d s *ᵥ psi)
      ((Complex.I • nsHamiltonian d) *ᵥ (nsFlowUnitary d t *ᵥ psi)) t := by sorry
