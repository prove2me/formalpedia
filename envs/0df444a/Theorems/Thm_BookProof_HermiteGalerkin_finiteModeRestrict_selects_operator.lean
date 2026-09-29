-- Prove2me | Theorems.Thm_BookProof_HermiteGalerkin_finiteModeRestrict_selects_operator
-- name    : BookProof.HermiteGalerkin.finiteModeRestrict_selects_operator
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-13T00:20:03.074228+00:00
-- url     : https://prove2.me/theorems/1a5c4694-be8b-4eac-96fd-7b4c317c7927
-- title:
--   The Lean 4 theorem `finiteModeRestrict_selects_operator` in the `ChapterHermiteGalerkinFriedrichs` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `finiteModeRestrict_selects_operator` in the `ChapterHermiteGalerkinFriedrichs` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteGalerkinFriedrichs.lean

-- Generated from ChapterHermiteGalerkinFriedrichs.lean — theorem BookProof.HermiteGalerkin.finiteModeRestrict_selects_operator
import Mathlib
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
open BookProof.HermiteGalerkin












open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit
open Filter Topology



variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]






variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]


















variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]



variable {D : Submodule ℂ F}












variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]









variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]










variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.HermiteGalerkin.finiteModeRestrict_selects_operator (A₀ : F →L[ℂ] F) (hsa : IsSelfAdjoint A₀)
    (hposA : ∀ u : F, 0 ≤ (inner ℂ u (A₀ u) : ℂ).re) (b : HilbertBasis ℕ ℂ F) :
    IsPositiveSelfAdjointExtension (finiteModeRestrict A₀ b) (topRestrict A₀) ∧
      (∀ (B : (⊤ : Submodule ℂ F) →ₗ[ℂ] F),
        IsPositiveSelfAdjointExtension (finiteModeRestrict A₀ b) B →
        ∀ x : F, B ⟨x, trivial⟩ = A₀ x) ∧
      (∀ u : F, Tendsto (fun m : ℕ => galerkinCompression A₀ b m u) atTop (nhds (A₀ u))) ∧
      (∀ z : ℂ, z.im ≠ 0 → ∀ u : F,
        Tendsto (fun m : ℕ => resolvent (galerkinCompression A₀ b m) z u) atTop
          (nhds (resolvent A₀ z u))) := by sorry
