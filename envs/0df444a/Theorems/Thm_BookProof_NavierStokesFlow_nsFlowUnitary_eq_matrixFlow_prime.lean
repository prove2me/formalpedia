-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_nsFlowUnitary_eq_matrixFlow_prime
-- name    : BookProof.NavierStokesFlow.nsFlowUnitary_eq_matrixFlow_prime
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-11T19:16:10.293022+00:00
-- url     : https://prove2.me/theorems/4d620acd-530d-401b-8c82-fb4cfa478f6e
-- title:
--   BookProof.NavierStokesFlow.nsFlowUnitary_eq_matrixFlow'
-- statement:
--   BookProof.NavierStokesFlow.nsFlowUnitary_eq_matrixFlow'

-- Generated from ChapterNavierStokesCauchy.lean — theorem BookProof.NavierStokesFlow.nsFlowUnitary_eq_matrixFlow'
import Mathlib
import Definitions.Def_ChapterNavierStokesCauchy
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow


open scoped BigOperators Matrix Matrix.Norms.Operator

variable {n : ℕ}
variable {n : ℕ} (d : NSTruncation n)

theorem BookProof.NavierStokesFlow.nsFlowUnitary_eq_matrixFlow_prime (t : ℝ) :
    HasDerivAt (nsFlowUnitary d) (nsFlowUnitary d t * (Complex.I • nsHamiltonian d)) t := by sorry
