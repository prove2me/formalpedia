-- Prove2me | Theorems.Thm_BookProof_EsaClosure_hashimoto_multishift_selects_esa
-- name    : BookProof.EsaClosure.hashimoto_multishift_selects_esa
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-13T10:02:51.407388+00:00
-- url     : https://prove2.me/theorems/c2cce2b5-00c1-43b2-8fde-f6a7f24fcd19
-- title:
--   The Lean 4 theorem `hashimoto_multishift_selects_esa` in the `ChapterEsaClosure` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `hashimoto_multishift_selects_esa` in the `ChapterEsaClosure` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterEsaClosure.lean

-- Generated from ChapterEsaClosure.lean — theorem BookProof.EsaClosure.hashimoto_multishift_selects_esa
import Mathlib
import Definitions.Def_ChapterEsaClosure
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Definitions.Def_ChapterSirkBandLedger
import Definitions.Def_ChapterNavierStokesDiffHashimoto
import Definitions.Def_ChapterHashimotoComplexShifts
open BookProof.EsaClosure



open Filter Topology


open BookProof.FarisLavine BookProof.NavierStokesFlow BookProof.HashimotoShiftInvert
open BookProof.HermiteGalerkin
open BookProof.YangMillsFriedrichs

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}




variable [CompleteSpace F]





variable [CompleteSpace F]

theorem BookProof.EsaClosure.hashimoto_multishift_selects_esa (b : HilbertBasis ℕ ℂ F) (T : D →ₗ[ℂ] F)
    (hdense : Dense (D : Set F)) (hsym : SymmetricOn D T) (hesa : EssentiallySelfAdjointOn D T)
    (γ : ℕ → ℂ) (hγ : ∀ j, (γ j).im ≠ 0) :
    ∃ (Dom : Submodule ℂ F) (A : Dom →ₗ[ℂ] F) (X : ℕ → F →L[ℂ] F),
      IsSelfAdjointExtension T A ∧
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
