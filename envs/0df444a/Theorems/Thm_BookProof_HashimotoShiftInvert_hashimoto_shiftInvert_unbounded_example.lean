-- Prove2me | Theorems.Thm_BookProof_HashimotoShiftInvert_hashimoto_shiftInvert_unbounded_example
-- name    : BookProof.HashimotoShiftInvert.hashimoto_shiftInvert_unbounded_example
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-03T15:20:47.40531+00:00
-- url     : https://prove2.me/theorems/21b6ab40-43f7-4ed1-be53-73c22816df5b
-- title:
--   The Lean 4 theorem `hashimoto_shiftInvert_unbounded_example` in the `ChapterHashimotoShiftInvert` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `hashimoto_shiftInvert_unbounded_example` in the `ChapterHashimotoShiftInvert` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHashimotoShiftInvert.lean

-- Generated from ChapterHashimotoShiftInvert.lean — theorem BookProof.HashimotoShiftInvert.hashimoto_shiftInvert_unbounded_example
import Mathlib
import Definitions.Def_ChapterHashimotoShiftInvert
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterComplexShiftCore
open scoped lp
open BookProof.HermiteGalerkin
open BookProof.HashimotoShiftInvert
open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit
open Filter Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {Dom : Submodule ℂ F}
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  {Dom : Submodule ℂ F}
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.HashimotoShiftInvert.hashimoto_shiftInvert_unbounded_example :
    IsShiftInvert ell2UnboundedExample 1 ell2ShiftInvert ∧
    ‖ell2ShiftInvert‖ ≤ 1 ∧ IsSelfAdjoint ell2ShiftInvert ∧
    (∀ u : ℓ²(ℕ, ℂ), Tendsto
      (fun m : ℕ => galerkinCompression ell2ShiftInvert ell2Basis m u) atTop
        (nhds (ell2ShiftInvert u))) ∧
    (∀ z : ℂ, z.im ≠ 0 → ∀ u : ℓ²(ℕ, ℂ), Tendsto
      (fun m : ℕ => resolvent (galerkinCompression ell2ShiftInvert ell2Basis m) z u) atTop
        (nhds (resolvent ell2ShiftInvert z u))) ∧
    (∀ (Dom' : Submodule ℂ (ℓ²(ℕ, ℂ))) (A' : Dom' →ₗ[ℂ] ℓ²(ℕ, ℂ)),
      IsShiftInvert A' 1 ell2ShiftInvert →
      Dom' = LinearMap.range (ell2ShiftInvert : ℓ²(ℕ, ℂ) →ₗ[ℂ] ℓ²(ℕ, ℂ))) ∧
    (∀ C : ℝ, ∃ x : finiteModeDomain ell2Basis,
      C * ‖(x : ℓ²(ℕ, ℂ))‖ < ‖ell2ExampleMatrix x‖) := by sorry
