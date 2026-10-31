-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_nsFlow_hasDerivAt
-- name    : BookProof.NavierStokesFlow.nsFlow_hasDerivAt
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-30T12:06:58.172637+00:00
-- url     : https://prove2.me/theorems/bd9ff7e7-74ba-46c1-b558-4120ba1d5caf
-- title:
--   The Lean 4 theorem `nsFlow_hasDerivAt` in the `ChapterNavierStokesCauchy` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `nsFlow_hasDerivAt` in the `ChapterNavierStokesCauchy` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesCauchy.lean

-- Generated from ChapterNavierStokesCauchy.lean — theorem BookProof.NavierStokesFlow.nsFlow_hasDerivAt
import Mathlib
import Definitions.Def_ChapterNavierStokesCauchy
open BookProof.NavierStokesFlow









open scoped BigOperators Matrix Matrix.Norms.Operator




variable {n : ℕ}

















variable {n : ℕ} (d : NSTruncation n)

theorem BookProof.NavierStokesFlow.nsFlow_hasDerivAt (t : ℝ) :
    HasDerivAt (nsFlowUnitary d) (nsFlowUnitary d t * (Complex.I • nsHamiltonian d)) t := by sorry
