-- Prove2me | Theorems.Thm_BookProof_HermiteGalerkin_resolvent_tendsto_of_strong_tendsto
-- name    : BookProof.HermiteGalerkin.resolvent_tendsto_of_strong_tendsto
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:29:53.347974+00:00
-- url     : https://prove2.me/theorems/285d2464-6c6d-4cc2-8389-f141ca67a376
-- title:
--   The Lean 4 theorem `resolvent_tendsto_of_strong_tendsto` in the `ChapterHermiteGalerkinFriedrichs` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `resolvent_tendsto_of_strong_tendsto` in the `ChapterHermiteGalerkinFriedrichs` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteGalerkinFriedrichs.lean

-- Generated from ChapterHermiteGalerkinFriedrichs.lean — theorem BookProof.HermiteGalerkin.resolvent_tendsto_of_strong_tendsto
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

theorem BookProof.HermiteGalerkin.resolvent_tendsto_of_strong_tendsto (T : ℕ → F →L[ℂ] F) (A : F →L[ℂ] F)
    (hT : ∀ n, IsSelfAdjoint (T n)) (hA : IsSelfAdjoint A) {z : ℂ} (hz : z.im ≠ 0)
    (hconv : ∀ u : F, Tendsto (fun n : ℕ => T n u) atTop (nhds (A u))) (u : F) :
    Tendsto (fun n : ℕ => resolvent (T n) z u) atTop (nhds (resolvent A z u)) := by sorry
