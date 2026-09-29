-- Prove2me | Theorems.Thm_BookProof_HashimotoShiftInvert_hashimoto_multishift_selects_friedrichs
-- name    : BookProof.HashimotoShiftInvert.hashimoto_multishift_selects_friedrichs
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:54:43.882254+00:00
-- url     : https://prove2.me/theorems/cede9bab-1c46-4b79-a6c6-f2f570ab96aa
-- title:
--   The Lean 4 theorem `hashimoto_multishift_selects_friedrichs` in the `ChapterHashimotoComplexShifts` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `hashimoto_multishift_selects_friedrichs` in the `ChapterHashimotoComplexShifts` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHashimotoComplexShifts.lean

-- Generated from ChapterHashimotoComplexShifts.lean — theorem BookProof.HashimotoShiftInvert.hashimoto_multishift_selects_friedrichs
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

theorem BookProof.HashimotoShiftInvert.hashimoto_multishift_selects_friedrichs (b : HilbertBasis ℕ ℂ F)
    (H : finiteModeDomain b →ₗ[ℂ] F) {Dom : Submodule ℂ F} (A : Dom →ₗ[ℂ] F)
    (hA : IsPositiveSelfAdjointExtension H A) (γ : ℕ → ℂ) (hγ : ∀ j, (γ j).im ≠ 0) :
    ∃ X : ℕ → F →L[ℂ] F,
      (∀ j, IsShiftInvertC A (γ j) (X j)) ∧
      (∀ j, ‖X j‖ ≤ |(γ j).im|⁻¹) ∧
      (∀ j, Dom = LinearMap.range ((X j : F →ₗ[ℂ] F))) ∧
      (∀ j k u, X j u - X k u = (γ k - γ j) • X j (X k u)) ∧
      (∀ j k, X j ∘L X k = X k ∘L X j) ∧
      (∀ j m, X j ∘L (ContinuousLinearMap.id ℂ F - (γ m - γ j) • X m) = X m) ∧
      (∀ m v k, sirkDen (X m) (fun i => γ m - γ i) k (rkVec X v k) = (X m ^ k) v) ∧
      (∀ j u, Tendsto (fun n : ℕ => galerkinCompression (X j) b n u) atTop (nhds (X j u))) ∧
      (∀ j (Dom' : Submodule ℂ F) (A' : Dom' →ₗ[ℂ] F), IsShiftInvertC A' (γ j) (X j) →
        Dom' = Dom ∧ ∀ (x : F) (hx : x ∈ Dom) (hx' : x ∈ Dom'), A' ⟨x, hx'⟩ = A ⟨x, hx⟩) := by sorry
