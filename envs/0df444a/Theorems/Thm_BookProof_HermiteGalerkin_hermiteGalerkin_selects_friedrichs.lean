-- Prove2me | Theorems.Thm_BookProof_HermiteGalerkin_hermiteGalerkin_selects_friedrichs
-- name    : BookProof.HermiteGalerkin.hermiteGalerkin_selects_friedrichs
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-13T00:19:23.663859+00:00
-- url     : https://prove2.me/theorems/2fcda437-eafe-4d8d-8435-7ba79051f658
-- title:
--   The Lean 4 theorem `hermiteGalerkin_selects_friedrichs` in the `ChapterHermiteGalerkinFriedrichs` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `hermiteGalerkin_selects_friedrichs` in the `ChapterHermiteGalerkinFriedrichs` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteGalerkinFriedrichs.lean

-- Generated from ChapterHermiteGalerkinFriedrichs.lean — theorem BookProof.HermiteGalerkin.hermiteGalerkin_selects_friedrichs
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

theorem BookProof.HermiteGalerkin.hermiteGalerkin_selects_friedrichs (b : HilbertBasis ℕ ℂ F)
    (H : finiteModeDomain b →ₗ[ℂ] F) (hsym : SymmetricOn (finiteModeDomain b) H)
    (hpos : ∀ x : finiteModeDomain b, 0 ≤ quadForm H x)
    (C : ℝ) (hbd : ∀ x : finiteModeDomain b, ‖H x‖ ≤ C * ‖(x : F)‖) :
    ∃ A : F →L[ℂ] F,
      (∀ x : finiteModeDomain b, A (x : F) = H x) ∧
      IsPositiveSelfAdjointExtension H (topRestrict A) ∧
      (∀ (B : (⊤ : Submodule ℂ F) →ₗ[ℂ] F), IsPositiveSelfAdjointExtension H B →
        ∀ x : F, B ⟨x, trivial⟩ = A x) ∧
      (∀ u : F, Tendsto (fun m : ℕ => galerkinCompression A b m u) atTop (nhds (A u))) ∧
      (∀ (z : ℂ), z.im ≠ 0 → ∀ u : F,
        Tendsto (fun m : ℕ => resolvent (galerkinCompression A b m) z u) atTop
          (nhds (resolvent A z u))) := by sorry
