-- Prove2me | Theorems.Thm_BookProof_HermiteGalerkin_isSelfAdjoint_galerkinCompression
-- name    : BookProof.HermiteGalerkin.isSelfAdjoint_galerkinCompression
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T18:33:06.601991+00:00
-- url     : https://prove2.me/theorems/4a984d87-27bd-4111-933f-74c985725840
-- title:
--   The Lean 4 theorem `isSelfAdjoint_galerkinCompression` in the `ChapterHermiteGalerkinFriedrichs` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `isSelfAdjoint_galerkinCompression` in the `ChapterHermiteGalerkinFriedrichs` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteGalerkinFriedrichs.lean

-- Generated from ChapterHermiteGalerkinFriedrichs.lean — theorem BookProof.HermiteGalerkin.isSelfAdjoint_galerkinCompression
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

theorem BookProof.HermiteGalerkin.isSelfAdjoint_galerkinCompression {A : F →L[ℂ] F} (hA : IsSelfAdjoint A)
    (b : HilbertBasis ℕ ℂ F) (m : ℕ) : IsSelfAdjoint (galerkinCompression A b m) := by sorry
