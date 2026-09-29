-- Prove2me | Theorems.Thm_BookProof_HermiteGalerkin_positive_selfadjoint_extension_unique
-- name    : BookProof.HermiteGalerkin.positive_selfadjoint_extension_unique
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T18:34:36.046284+00:00
-- url     : https://prove2.me/theorems/3ae96ced-0ad0-4095-b651-1059549cc2df
-- title:
--   The Lean 4 theorem `positive_selfadjoint_extension_unique` in the `ChapterHermiteGalerkinFriedrichs` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `positive_selfadjoint_extension_unique` in the `ChapterHermiteGalerkinFriedrichs` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteGalerkinFriedrichs.lean

-- Generated from ChapterHermiteGalerkinFriedrichs.lean — theorem BookProof.HermiteGalerkin.positive_selfadjoint_extension_unique
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

theorem BookProof.HermiteGalerkin.positive_selfadjoint_extension_unique {D : Submodule ℂ F} (H : D →ₗ[ℂ] F)
    (hdense : Dense (D : Set F)) (A : F →L[ℂ] F) (hAH : ∀ x : D, A (x : F) = H x)
    (B : (⊤ : Submodule ℂ F) →ₗ[ℂ] F) (hB : IsPositiveSelfAdjointExtension H B) (x : F) :
    B ⟨x, trivial⟩ = A x := by sorry
