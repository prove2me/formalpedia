-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_nsFlow_noBlowup
-- name    : BookProof.NavierStokesFlow.nsFlow_noBlowup
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-02T23:43:28.529328+00:00
-- url     : https://prove2.me/theorems/036ae199-71c1-44fd-8307-f4f4644c16ab
-- title:
--   The Lean 4 theorem `nsFlow_noBlowup` in the `ChapterNavierStokesFlow` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `nsFlow_noBlowup` in the `ChapterNavierStokesFlow` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFlow.lean — theorem BookProof.NavierStokesFlow.nsFlow_noBlowup
import Mathlib
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow

variable {E : Type*} [AddCommGroup E] [Module ℂ E] {ι : Type*} [Fintype ι]
variable {n : ℕ} (L : LagrangianNS n)
variable {n : ℕ} (d : NSTruncation n)


open scoped BigOperators Matrix Kronecker ComplexOrder TensorProduct

theorem BookProof.NavierStokesFlow.nsFlow_noBlowup (t : ℝ) (psi : Fin n → ℂ) (k : Fin n) :
    ‖(nsFlowUnitary d t *ᵥ psi) k‖ ^ 2 ≤ ∑ a, ‖psi a‖ ^ 2 := by sorry
