-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_nsFlow_groupOnEvolved
-- name    : BookProof.NavierStokesFlow.nsFlow_groupOnEvolved
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-02T23:22:09.478384+00:00
-- url     : https://prove2.me/theorems/cbffcb8f-ab2f-444b-a3f9-d86cb923f772
-- title:
--   The Lean 4 theorem `nsFlow_groupOnEvolved` in the `ChapterNavierStokesFlow` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `nsFlow_groupOnEvolved` in the `ChapterNavierStokesFlow` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFlow.lean — theorem BookProof.NavierStokesFlow.nsFlow_groupOnEvolved
import Mathlib
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow

variable {E : Type*} [AddCommGroup E] [Module ℂ E] {ι : Type*} [Fintype ι]
variable {n : ℕ} (L : LagrangianNS n)
variable {n : ℕ} (d : NSTruncation n)


open scoped BigOperators Matrix Kronecker ComplexOrder TensorProduct

theorem BookProof.NavierStokesFlow.nsFlow_groupOnEvolved (t₁ t₂ : ℝ) (psi : Fin n → ℂ) :
    nsFlowUnitary d t₁ *ᵥ (nsFlowUnitary d t₂ *ᵥ psi) = nsFlowUnitary d (t₁ + t₂) *ᵥ psi := by sorry
