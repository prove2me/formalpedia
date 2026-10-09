-- Prove2me | Theorems.Thm_BookProof_ChapterGravityTimeProj_timeProj_mul_spatialProj
-- name    : BookProof.ChapterGravityTimeProj.timeProj_mul_spatialProj
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T11:52:21.794006+00:00
-- url     : https://prove2.me/theorems/09f93ee8-fbed-469f-86ca-753b9674c1ac
-- title:
--   `BookProof.ChapterGravityTimeProj.timeProj_mul_spatialProj` (v : Fin 4 → ℝ) (hv : minkSq v = -1) : timeProj v * spatialProj v = 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGravityTimeProj`.
--
--   `BookProof.ChapterGravityTimeProj.timeProj_mul_spatialProj` (v : Fin 4 → ℝ) (hv : minkSq v = -1) : timeProj v * spatialProj v = 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGravityTimeProj.timeProj_mul_spatialProj`.

-- Generated from ChapterGravityTimeProj.lean — theorem BookProof.ChapterGravityTimeProj.timeProj_mul_spatialProj
import Mathlib
import Definitions.Def_ChapterGravityTimeProj
import Definitions.Def_ChapterGravityProjector
open BookProof.ChapterGravityProjector
open BookProof.ChapterGravityTimeProj



open Matrix
open scoped BigOperators
open BookProof.ChapterGravityProjector

theorem BookProof.ChapterGravityTimeProj.timeProj_mul_spatialProj (v : Fin 4 → ℝ) (hv : minkSq v = -1) :
    timeProj v * spatialProj v = 0 := by sorry
