-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_field_evaluates_to_value
-- name    : BookProof.NavierStokesFlow.field_evaluates_to_value
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T11:53:05.70326+00:00
-- url     : https://prove2.me/theorems/274f9124-7bcb-40de-bb5a-a7cb5ac68cb5
-- title:
--   The Lean 4 theorem `field_evaluates_to_value` in the `ChapterNavierStokesFlow` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `field_evaluates_to_value` in the `ChapterNavierStokesFlow` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFlow.lean — theorem BookProof.NavierStokesFlow.field_evaluates_to_value
import Mathlib
import Definitions.Def_ChapterNavierStokesFlow
open BookProof.NavierStokesFlow


open scoped BigOperators Matrix Kronecker ComplexOrder TensorProduct

variable {E : Type*} [AddCommGroup E] [Module ℂ E] {ι : Type*} [Fintype ι]

theorem BookProof.NavierStokesFlow.field_evaluates_to_value (phi : E →ₗ[ℂ] E) (phiD : ι → E →ₗ[ℂ] E)
    (X : ι → E →ₗ[ℂ] E) (x : ι → ℂ) (v : E) (hv : ∀ i, X i v = x i • v) :
    fieldTaylor phi phiD X x v = phi v := by sorry
