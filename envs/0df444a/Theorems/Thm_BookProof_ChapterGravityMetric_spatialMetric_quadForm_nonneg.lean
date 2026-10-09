-- Prove2me | Theorems.Thm_BookProof_ChapterGravityMetric_spatialMetric_quadForm_nonneg
-- name    : BookProof.ChapterGravityMetric.spatialMetric_quadForm_nonneg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T13:00:07.675974+00:00
-- url     : https://prove2.me/theorems/16a6476f-be19-4820-914f-81c78892097b
-- title:
--   `BookProof.ChapterGravityMetric.spatialMetric_quadForm_nonneg` (v x : Fin 4 → ℝ) (hv : minkSq v = -1) : 0 ≤ x ⬝ᵥ ((spatialMetric v).mulVec x)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGravityMetric`.
--
--   `BookProof.ChapterGravityMetric.spatialMetric_quadForm_nonneg` (v x : Fin 4 → ℝ) (hv : minkSq v = -1) : 0 ≤ x ⬝ᵥ ((spatialMetric v).mulVec x)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGravityMetric.spatialMetric_quadForm_nonneg`.

-- Generated from ChapterGravityMetric.lean — theorem BookProof.ChapterGravityMetric.spatialMetric_quadForm_nonneg
import Mathlib
import Definitions.Def_ChapterGravityMetric
import Definitions.Def_ChapterGravityProjector
open BookProof.ChapterGravityProjector
open BookProof.ChapterGravityMetric



open Matrix
open scoped BigOperators
open BookProof.ChapterGravityProjector

theorem BookProof.ChapterGravityMetric.spatialMetric_quadForm_nonneg (v x : Fin 4 → ℝ) (hv : minkSq v = -1) :
    0 ≤ x ⬝ᵥ ((spatialMetric v).mulVec x) := by sorry
