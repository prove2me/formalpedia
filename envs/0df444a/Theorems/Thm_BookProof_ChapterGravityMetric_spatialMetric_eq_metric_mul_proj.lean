-- Prove2me | Theorems.Thm_BookProof_ChapterGravityMetric_spatialMetric_eq_metric_mul_proj
-- name    : BookProof.ChapterGravityMetric.spatialMetric_eq_metric_mul_proj
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T13:00:13.110074+00:00
-- url     : https://prove2.me/theorems/0e81d575-de64-4ad4-8c77-a5f3a87416d3
-- title:
--   `BookProof.ChapterGravityMetric.spatialMetric_eq_metric_mul_proj` (v : Fin 4 → ℝ) : spatialMetric v = metric * spatialProj v
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGravityMetric`.
--
--   `BookProof.ChapterGravityMetric.spatialMetric_eq_metric_mul_proj` (v : Fin 4 → ℝ) : spatialMetric v = metric * spatialProj v
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGravityMetric.spatialMetric_eq_metric_mul_proj`.

-- Generated from ChapterGravityMetric.lean — theorem BookProof.ChapterGravityMetric.spatialMetric_eq_metric_mul_proj
import Mathlib
import Definitions.Def_ChapterGravityMetric
import Definitions.Def_ChapterGravityProjector
open BookProof.ChapterGravityProjector
open BookProof.ChapterGravityMetric



open Matrix
open scoped BigOperators
open BookProof.ChapterGravityProjector

theorem BookProof.ChapterGravityMetric.spatialMetric_eq_metric_mul_proj (v : Fin 4 → ℝ) :
    spatialMetric v = metric * spatialProj v := by sorry
