-- Prove2me | Theorems.Thm_BookProof_ChapterGravityInvMetric_invSpatialMetric_mul_spatialMetric
-- name    : BookProof.ChapterGravityInvMetric.invSpatialMetric_mul_spatialMetric
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T12:58:24.40317+00:00
-- url     : https://prove2.me/theorems/ac60a228-a85f-458d-988a-3ade9012d3b9
-- title:
--   `BookProof.ChapterGravityInvMetric.invSpatialMetric_mul_spatialMetric` (v : Fin 4 → ℝ) (hv : minkSq v = -1) : invSpatialMetric v * spatialMetric v = spatialProj v
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGravityInvMetric`.
--
--   `BookProof.ChapterGravityInvMetric.invSpatialMetric_mul_spatialMetric` (v : Fin 4 → ℝ) (hv : minkSq v = -1) : invSpatialMetric v * spatialMetric v = spatialProj v
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGravityInvMetric.invSpatialMetric_mul_spatialMetric`.

-- Generated from ChapterGravityInvMetric.lean — theorem BookProof.ChapterGravityInvMetric.invSpatialMetric_mul_spatialMetric
import Mathlib
import Definitions.Def_ChapterGravityInvMetric
import Definitions.Def_ChapterGravityMetric
import Definitions.Def_ChapterGravityProjector
open BookProof.ChapterGravityMetric
open BookProof.ChapterGravityProjector
open BookProof.ChapterGravityInvMetric



open Matrix
open scoped BigOperators
open BookProof.ChapterGravityProjector
open BookProof.ChapterGravityMetric

theorem BookProof.ChapterGravityInvMetric.invSpatialMetric_mul_spatialMetric (v : Fin 4 → ℝ) (hv : minkSq v = -1) :
    invSpatialMetric v * spatialMetric v = spatialProj v := by sorry
