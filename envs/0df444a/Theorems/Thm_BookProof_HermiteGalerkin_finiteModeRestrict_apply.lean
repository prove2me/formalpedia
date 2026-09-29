-- Prove2me | Theorems.Thm_BookProof_HermiteGalerkin_finiteModeRestrict_apply
-- name    : BookProof.HermiteGalerkin.finiteModeRestrict_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T18:30:35.527743+00:00
-- url     : https://prove2.me/theorems/cbe13f98-26d2-4196-8bab-493de5d38c54
-- title:
--   The Lean 4 theorem `finiteModeRestrict_apply` in the `ChapterHermiteGalerkinFriedrichs` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `finiteModeRestrict_apply` in the `ChapterHermiteGalerkinFriedrichs` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteGalerkinFriedrichs.lean

-- Generated from ChapterHermiteGalerkinFriedrichs.lean — theorem BookProof.HermiteGalerkin.finiteModeRestrict_apply
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

theorem BookProof.HermiteGalerkin.finiteModeRestrict_apply (A₀ : F →L[ℂ] F) (b : HilbertBasis ℕ ℂ F)
    (x : finiteModeDomain b) : finiteModeRestrict A₀ b x = A₀ (x : F) := by sorry
