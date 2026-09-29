-- Prove2me | Theorems.Thm_BookProof_HermiteGalerkin_galerkinResolvent_tendsto
-- name    : BookProof.HermiteGalerkin.galerkinResolvent_tendsto
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:56:29.962576+00:00
-- url     : https://prove2.me/theorems/da068bb0-f3e3-4cfd-a50e-ea30ed0f6e17
-- title:
--   The Lean 4 theorem `galerkinResolvent_tendsto` in the `ChapterHermiteGalerkinFriedrichs` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `galerkinResolvent_tendsto` in the `ChapterHermiteGalerkinFriedrichs` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteGalerkinFriedrichs.lean

-- Generated from ChapterHermiteGalerkinFriedrichs.lean — theorem BookProof.HermiteGalerkin.galerkinResolvent_tendsto
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

theorem BookProof.HermiteGalerkin.galerkinResolvent_tendsto {A : F →L[ℂ] F} (hA : IsSelfAdjoint A)
    (b : HilbertBasis ℕ ℂ F) {z : ℂ} (hz : z.im ≠ 0) (u : F) :
    Tendsto (fun m : ℕ => resolvent (galerkinCompression A b m) z u) atTop
      (nhds (resolvent A z u)) := by sorry
