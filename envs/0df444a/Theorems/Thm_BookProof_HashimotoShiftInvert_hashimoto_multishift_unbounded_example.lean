-- Prove2me | Theorems.Thm_BookProof_HashimotoShiftInvert_hashimoto_multishift_unbounded_example
-- name    : BookProof.HashimotoShiftInvert.hashimoto_multishift_unbounded_example
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:54:29.053604+00:00
-- url     : https://prove2.me/theorems/993b3a9b-8aef-4bf7-b8bc-abe5e0a0e490
-- title:
--   The Lean 4 theorem `hashimoto_multishift_unbounded_example` in the `ChapterHashimotoComplexShifts` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `hashimoto_multishift_unbounded_example` in the `ChapterHashimotoComplexShifts` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHashimotoComplexShifts.lean

-- Generated from ChapterHashimotoComplexShifts.lean — theorem BookProof.HashimotoShiftInvert.hashimoto_multishift_unbounded_example
import Mathlib
import Definitions.Def_ChapterHashimotoComplexShifts
open BookProof.HashimotoShiftInvert


















open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit
open BookProof.HermiteGalerkin
open Filter Topology




variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {Dom : Submodule ℂ F}


















variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {Dom : Submodule ℂ F}




















variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]







variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]








open scoped ENNReal InnerProductSpace lp

theorem BookProof.HashimotoShiftInvert.hashimoto_multishift_unbounded_example (γ : ℕ → ℂ) (hγ : ∀ j, (γ j).im ≠ 0) :
    ∃ X : ℕ → ℓ²(ℕ, ℂ) →L[ℂ] ℓ²(ℕ, ℂ),
      (∀ j u n, ((X j u : ℓ²(ℕ, ℂ)) : ℕ → ℂ) n = (u : ℕ → ℂ) n / (γ j - (n : ℂ))) ∧
      (∀ j, IsShiftInvertC ell2UnboundedExample (γ j) (X j)) ∧
      (∀ j, ‖X j‖ ≤ |(γ j).im|⁻¹) ∧
      (∀ j k u, X j u - X k u = (γ k - γ j) • X j (X k u)) ∧
      (∀ j k, X j ∘L X k = X k ∘L X j) ∧
      (∀ j m, X j ∘L (ContinuousLinearMap.id ℂ (ℓ²(ℕ, ℂ)) - (γ m - γ j) • X m) = X m) ∧
      (∀ m v k, sirkDen (X m) (fun i => γ m - γ i) k (rkVec X v k) = (X m ^ k) v) ∧
      (∀ j u, Tendsto (fun n : ℕ => galerkinCompression (X j) ell2Basis n u) atTop
        (nhds (X j u))) ∧
      (∀ j (Dom' : Submodule ℂ (ℓ²(ℕ, ℂ))) (A' : Dom' →ₗ[ℂ] ℓ²(ℕ, ℂ)),
        IsShiftInvertC A' (γ j) (X j) →
        Dom' = LinearMap.range (ell2ShiftInvert : ℓ²(ℕ, ℂ) →ₗ[ℂ] ℓ²(ℕ, ℂ))) ∧
      (∀ C : ℝ, ∃ x : finiteModeDomain ell2Basis,
        C * ‖(x : ℓ²(ℕ, ℂ))‖ < ‖ell2ExampleMatrix x‖) := by sorry
