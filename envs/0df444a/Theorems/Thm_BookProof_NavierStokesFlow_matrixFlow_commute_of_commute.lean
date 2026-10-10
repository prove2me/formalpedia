-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_matrixFlow_commute_of_commute
-- name    : BookProof.NavierStokesFlow.matrixFlow_commute_of_commute
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T06:38:20.472972+00:00
-- url     : https://prove2.me/theorems/326f579e-7af4-40f8-846d-95c52ad597fe
-- title:
--   `BookProof.NavierStokesFlow.matrixFlow_commute_of_commute` (t : ℝ) : nsFlowUnitary d t * nsHamiltonian d = nsHamiltonian d * nsFlowUnitary d t
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesCauchy`.
--
--   `BookProof.NavierStokesFlow.matrixFlow_commute_of_commute` (t : ℝ) : nsFlowUnitary d t * nsHamiltonian d = nsHamiltonian d * nsFlowUnitary d t
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.matrixFlow_commute_of_commute`.

-- Generated from ChapterNavierStokesCauchy.lean — theorem BookProof.NavierStokesFlow.matrixFlow_commute_of_commute
import Mathlib
import Definitions.Def_ChapterNavierStokesCauchy
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow


open scoped BigOperators Matrix Matrix.Norms.Operator

variable {n : ℕ}
variable {n : ℕ} (d : NSTruncation n)

theorem BookProof.NavierStokesFlow.matrixFlow_commute_of_commute (t : ℝ) :
    nsFlowUnitary d t * nsHamiltonian d = nsHamiltonian d * nsFlowUnitary d t := by sorry
