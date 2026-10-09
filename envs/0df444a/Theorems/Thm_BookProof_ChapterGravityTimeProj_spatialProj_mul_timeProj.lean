-- Prove2me | Theorems.Thm_BookProof_ChapterGravityTimeProj_spatialProj_mul_timeProj
-- name    : BookProof.ChapterGravityTimeProj.spatialProj_mul_timeProj
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T11:52:12.836563+00:00
-- url     : https://prove2.me/theorems/4c29c4ec-49a5-48aa-9338-6d8e65279ff7
-- title:
--   `BookProof.ChapterGravityTimeProj.spatialProj_mul_timeProj` (v : Fin 4 → ℝ) (hv : minkSq v = -1) : spatialProj v * timeProj v = 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGravityTimeProj`.
--
--   `BookProof.ChapterGravityTimeProj.spatialProj_mul_timeProj` (v : Fin 4 → ℝ) (hv : minkSq v = -1) : spatialProj v * timeProj v = 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGravityTimeProj.spatialProj_mul_timeProj`.

-- Generated from ChapterGravityTimeProj.lean — theorem BookProof.ChapterGravityTimeProj.spatialProj_mul_timeProj
import Mathlib
import Definitions.Def_ChapterGravityTimeProj
import Definitions.Def_ChapterGravityProjector
open BookProof.ChapterGravityProjector
open BookProof.ChapterGravityTimeProj



open Matrix
open scoped BigOperators
open BookProof.ChapterGravityProjector

theorem BookProof.ChapterGravityTimeProj.spatialProj_mul_timeProj (v : Fin 4 → ℝ) (hv : minkSq v = -1) :
    spatialProj v * timeProj v = 0 := by sorry
