-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_nsFlow_unitary
-- name    : BookProof.NavierStokesFlow.nsFlow_unitary
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-02T23:25:27.913913+00:00
-- url     : https://prove2.me/theorems/628e0a01-6025-4f31-998d-6e91ffd2e0fb
-- title:
--   The Lean 4 theorem `nsFlow_unitary` in the `ChapterNavierStokesFlow` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `nsFlow_unitary` in the `ChapterNavierStokesFlow` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFlow.lean — theorem BookProof.NavierStokesFlow.nsFlow_unitary
import Mathlib
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterContinuityUnitary
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.ChapterContinuityUnitary
open BookProof.NavierStokesFlow

variable {E : Type*} [AddCommGroup E] [Module ℂ E] {ι : Type*} [Fintype ι]
variable {n : ℕ} (L : LagrangianNS n)
variable {n : ℕ} (d : NSTruncation n)


open scoped BigOperators Matrix Kronecker ComplexOrder TensorProduct

theorem BookProof.NavierStokesFlow.nsFlow_unitary (t : ℝ) : (nsFlowUnitary d t)ᴴ * nsFlowUnitary d t = 1 := by sorry
