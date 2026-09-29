-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_nsFlow_zero
-- name    : BookProof.NavierStokesFlow.nsFlow_zero
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T11:53:09.353773+00:00
-- url     : https://prove2.me/theorems/2f40df79-2d64-41be-8706-62b302d36128
-- title:
--   The Lean 4 theorem `nsFlow_zero` in the `ChapterNavierStokesFlow` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `nsFlow_zero` in the `ChapterNavierStokesFlow` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFlow.lean — theorem BookProof.NavierStokesFlow.nsFlow_zero
import Mathlib
import Definitions.Def_ChapterNavierStokesFlow
open BookProof.NavierStokesFlow


open scoped BigOperators Matrix Kronecker ComplexOrder TensorProduct

variable {n : ℕ} (d : NSTruncation n)

theorem BookProof.NavierStokesFlow.nsFlow_zero : nsFlowUnitary d 0 = 1 := by sorry
