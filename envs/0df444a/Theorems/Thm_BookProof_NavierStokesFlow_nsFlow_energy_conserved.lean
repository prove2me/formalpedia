-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_nsFlow_energy_conserved
-- name    : BookProof.NavierStokesFlow.nsFlow_energy_conserved
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T19:16:42.995327+00:00
-- url     : https://prove2.me/theorems/1846ac55-543c-4dc3-be2e-99b89c71c6f7
-- title:
--   `BookProof.NavierStokesFlow.nsFlow_energy_conserved` (t : ℝ) (psi : Fin n → ℂ) : star (nsFlowUnitary d t *ᵥ psi) ⬝ᵥ (nsHamiltonian d *ᵥ (nsFlowUnitary d t *ᵥ psi)) = star psi ⬝ᵥ (n
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesCauchy`.
--
--   `BookProof.NavierStokesFlow.nsFlow_energy_conserved` (t : ℝ) (psi : Fin n → ℂ) : star (nsFlowUnitary d t *ᵥ psi) ⬝ᵥ (nsHamiltonian d *ᵥ (nsFlowUnitary d t *ᵥ psi)) = star psi ⬝ᵥ (nsHamiltonian d *ᵥ psi)
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.nsFlow_energy_conserved`.

-- Generated from ChapterNavierStokesCauchy.lean — theorem BookProof.NavierStokesFlow.nsFlow_energy_conserved
import Mathlib
import Definitions.Def_ChapterNavierStokesCauchy
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow


open scoped BigOperators Matrix Matrix.Norms.Operator

variable {n : ℕ}
variable {n : ℕ} (d : NSTruncation n)

theorem BookProof.NavierStokesFlow.nsFlow_energy_conserved (t : ℝ) (psi : Fin n → ℂ) :
    star (nsFlowUnitary d t *ᵥ psi) ⬝ᵥ (nsHamiltonian d *ᵥ (nsFlowUnitary d t *ᵥ psi))
      = star psi ⬝ᵥ (nsHamiltonian d *ᵥ psi) := by sorry
