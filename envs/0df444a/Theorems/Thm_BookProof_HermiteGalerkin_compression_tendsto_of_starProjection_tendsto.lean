-- Prove2me | Theorems.Thm_BookProof_HermiteGalerkin_compression_tendsto_of_starProjection_tendsto
-- name    : BookProof.HermiteGalerkin.compression_tendsto_of_starProjection_tendsto
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T18:30:30.799528+00:00
-- url     : https://prove2.me/theorems/16b0a238-907e-4a8b-bed0-a80c0dc60e08
-- title:
--   The Lean 4 theorem `compression_tendsto_of_starProjection_tendsto` in the `ChapterHermiteGalerkinFriedrichs` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `compression_tendsto_of_starProjection_tendsto` in the `ChapterHermiteGalerkinFriedrichs` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteGalerkinFriedrichs.lean

-- Generated from ChapterHermiteGalerkinFriedrichs.lean — theorem BookProof.HermiteGalerkin.compression_tendsto_of_starProjection_tendsto
import Mathlib
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
open BookProof.HermiteGalerkin












open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit
open Filter Topology



variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem BookProof.HermiteGalerkin.compression_tendsto_of_starProjection_tendsto (K : ℕ → Submodule ℂ F)
    [∀ n, (K n).HasOrthogonalProjection] (A : F →L[ℂ] F)
    (hP : ∀ u : F, Tendsto (fun n : ℕ => (K n).starProjection u) atTop (nhds u)) (u : F) :
    Tendsto (fun n : ℕ => (K n).starProjection (A ((K n).starProjection u)))
      atTop (nhds (A u)) := by sorry
