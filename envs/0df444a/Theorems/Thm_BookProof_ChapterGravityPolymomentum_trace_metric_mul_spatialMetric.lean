-- Prove2me | Theorems.Thm_BookProof_ChapterGravityPolymomentum_trace_metric_mul_spatialMetric
-- name    : BookProof.ChapterGravityPolymomentum.trace_metric_mul_spatialMetric
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T11:46:28.872466+00:00
-- url     : https://prove2.me/theorems/11fa0c94-e124-4446-a2a7-9eb626312b9a
-- title:
--   `BookProof.ChapterGravityPolymomentum.trace_metric_mul_spatialMetric` (v : Fin 4 → ℝ) (hv : minkSq v = -1) : (metric * (metric + vecMulVec v v)).trace = 3
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGravityPolymomentum`.
--
--   `BookProof.ChapterGravityPolymomentum.trace_metric_mul_spatialMetric` (v : Fin 4 → ℝ) (hv : minkSq v = -1) : (metric * (metric + vecMulVec v v)).trace = 3
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGravityPolymomentum.trace_metric_mul_spatialMetric`.

-- Generated from ChapterGravityPolymomentum.lean — theorem BookProof.ChapterGravityPolymomentum.trace_metric_mul_spatialMetric
import Mathlib
import Definitions.Def_ChapterGravityPolymomentum
import Definitions.Def_ChapterGravityProjector
open BookProof.ChapterGravityProjector
open BookProof.ChapterGravityPolymomentum



open Matrix
open scoped BigOperators
open BookProof.ChapterGravityProjector

theorem BookProof.ChapterGravityPolymomentum.trace_metric_mul_spatialMetric (v : Fin 4 → ℝ) (hv : minkSq v = -1) :
    (metric * (metric + vecMulVec v v)).trace = 3 := by sorry
