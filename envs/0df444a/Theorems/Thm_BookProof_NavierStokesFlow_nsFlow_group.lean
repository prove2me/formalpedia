-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_nsFlow_group
-- name    : BookProof.NavierStokesFlow.nsFlow_group
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T11:53:02.383701+00:00
-- url     : https://prove2.me/theorems/9b80063f-7acb-4234-80ee-f5456c0fc582
-- title:
--   The Lean 4 theorem `nsFlow_group` in the `ChapterNavierStokesFlow` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `nsFlow_group` in the `ChapterNavierStokesFlow` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFlow.lean — theorem BookProof.NavierStokesFlow.nsFlow_group
import Mathlib
import Definitions.Def_ChapterNavierStokesFlow
open BookProof.NavierStokesFlow


open scoped BigOperators Matrix Kronecker ComplexOrder TensorProduct

variable {n : ℕ} (d : NSTruncation n)

theorem BookProof.NavierStokesFlow.nsFlow_group (s t : ℝ) :
    nsFlowUnitary d (s + t) = nsFlowUnitary d s * nsFlowUnitary d t := by sorry
