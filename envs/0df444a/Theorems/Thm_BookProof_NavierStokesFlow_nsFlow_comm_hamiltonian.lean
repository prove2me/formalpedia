-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_nsFlow_comm_hamiltonian
-- name    : BookProof.NavierStokesFlow.nsFlow_comm_hamiltonian
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T05:01:34.345986+00:00
-- url     : https://prove2.me/theorems/77e5cb28-9c68-4a00-a734-fa48e2fb0a41
-- title:
--   The Lean 4 theorem `nsFlow_comm_hamiltonian` in the `ChapterNavierStokesCauchy` chapter of the timepiece formalization
-- statement:
--   Formal statement of `BookProof.NavierStokesFlow.nsFlow_comm_hamiltonian` from the timepiece Lean 4 formalization.
-- source:
--   https://github.com/leonardopedro/timepiece

-- Generated from ChapterNavierStokesCauchy.lean — theorem BookProof.NavierStokesFlow.nsFlow_comm_hamiltonian
import Mathlib
import Definitions.Def_ChapterNavierStokesCauchy
open BookProof.NavierStokesFlow









open scoped BigOperators Matrix Matrix.Norms.Operator




variable {n : ℕ}

















variable {n : ℕ} (d : NSTruncation n)

theorem BookProof.NavierStokesFlow.nsFlow_comm_hamiltonian (t : ℝ) :
    nsFlowUnitary d t * nsHamiltonian d = nsHamiltonian d * nsFlowUnitary d t := by sorry
