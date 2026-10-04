-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_nsFlow_norm_preserving
-- name    : BookProof.NavierStokesFlow.nsFlow_norm_preserving
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-02T23:42:24.614601+00:00
-- url     : https://prove2.me/theorems/38893424-1937-4325-9c84-83a1d033fb7c
-- title:
--   The Lean 4 theorem `nsFlow_norm_preserving` in the `ChapterNavierStokesFlow` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `nsFlow_norm_preserving` in the `ChapterNavierStokesFlow` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFlow.lean — theorem BookProof.NavierStokesFlow.nsFlow_norm_preserving
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

theorem BookProof.NavierStokesFlow.nsFlow_norm_preserving (t : ℝ) (psi : Fin n → ℂ) :
    ∑ a, ‖(nsFlowUnitary d t *ᵥ psi) a‖ ^ 2 = ∑ a, ‖psi a‖ ^ 2 := by sorry
