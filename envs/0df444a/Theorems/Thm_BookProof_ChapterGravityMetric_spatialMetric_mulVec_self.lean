-- Prove2me | Theorems.Thm_BookProof_ChapterGravityMetric_spatialMetric_mulVec_self
-- name    : BookProof.ChapterGravityMetric.spatialMetric_mulVec_self
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T13:00:43.632911+00:00
-- url     : https://prove2.me/theorems/3fe990fc-2586-4f0b-9996-cf7ea3ceb1c1
-- title:
--   `BookProof.ChapterGravityMetric.spatialMetric_mulVec_self` (v : Fin 4 → ℝ) (hv : minkSq v = -1) : (spatialMetric v).mulVec v = 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGravityMetric`.
--
--   `BookProof.ChapterGravityMetric.spatialMetric_mulVec_self` (v : Fin 4 → ℝ) (hv : minkSq v = -1) : (spatialMetric v).mulVec v = 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGravityMetric.spatialMetric_mulVec_self`.

-- Generated from ChapterGravityMetric.lean — theorem BookProof.ChapterGravityMetric.spatialMetric_mulVec_self
import Mathlib
import Definitions.Def_ChapterGravityMetric
import Definitions.Def_ChapterGravityProjector
open BookProof.ChapterGravityProjector
open BookProof.ChapterGravityMetric



open Matrix
open scoped BigOperators
open BookProof.ChapterGravityProjector

theorem BookProof.ChapterGravityMetric.spatialMetric_mulVec_self (v : Fin 4 → ℝ) (hv : minkSq v = -1) :
    (spatialMetric v).mulVec v = 0 := by sorry
