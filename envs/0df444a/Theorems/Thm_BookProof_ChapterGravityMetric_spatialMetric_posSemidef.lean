-- Prove2me | Theorems.Thm_BookProof_ChapterGravityMetric_spatialMetric_posSemidef
-- name    : BookProof.ChapterGravityMetric.spatialMetric_posSemidef
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T13:00:41.296286+00:00
-- url     : https://prove2.me/theorems/a68ccd54-a2fa-4e6b-977a-262428ca6052
-- title:
--   `BookProof.ChapterGravityMetric.spatialMetric_posSemidef` (v : Fin 4 → ℝ) (hv : minkSq v = -1) : (spatialMetric v).PosSemidef
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGravityMetric`.
--
--   `BookProof.ChapterGravityMetric.spatialMetric_posSemidef` (v : Fin 4 → ℝ) (hv : minkSq v = -1) : (spatialMetric v).PosSemidef
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGravityMetric.spatialMetric_posSemidef`.

-- Generated from ChapterGravityMetric.lean — theorem BookProof.ChapterGravityMetric.spatialMetric_posSemidef
import Mathlib
import Definitions.Def_ChapterGravityMetric
import Definitions.Def_ChapterGravityProjector
open BookProof.ChapterGravityProjector
open BookProof.ChapterGravityMetric



open Matrix
open scoped BigOperators
open BookProof.ChapterGravityProjector

theorem BookProof.ChapterGravityMetric.spatialMetric_posSemidef (v : Fin 4 → ℝ) (hv : minkSq v = -1) :
    (spatialMetric v).PosSemidef := by sorry
