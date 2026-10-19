-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_nsFlowUnitary_eq_matrixFlow
-- name    : BookProof.NavierStokesFlow.nsFlowUnitary_eq_matrixFlow
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T19:16:18.281212+00:00
-- url     : https://prove2.me/theorems/0256c464-4b62-4d69-bcce-d4edfc13d3b4
-- title:
--   `BookProof.NavierStokesFlow.nsFlowUnitary_eq_matrixFlow` (t : ℝ) : nsFlowUnitary d t = matrixFlow (Complex.I • nsHamiltonian d) t
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesCauchy`.
--
--   `BookProof.NavierStokesFlow.nsFlowUnitary_eq_matrixFlow` (t : ℝ) : nsFlowUnitary d t = matrixFlow (Complex.I • nsHamiltonian d) t
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.nsFlowUnitary_eq_matrixFlow`.

-- Generated from ChapterNavierStokesCauchy.lean — theorem BookProof.NavierStokesFlow.nsFlowUnitary_eq_matrixFlow
import Mathlib
import Definitions.Def_ChapterNavierStokesCauchy
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow


open scoped BigOperators Matrix Matrix.Norms.Operator

variable {n : ℕ}
variable {n : ℕ} (d : NSTruncation n)

theorem BookProof.NavierStokesFlow.nsFlowUnitary_eq_matrixFlow (t : ℝ) :
    nsFlowUnitary d t = matrixFlow (Complex.I • nsHamiltonian d) t := by sorry
