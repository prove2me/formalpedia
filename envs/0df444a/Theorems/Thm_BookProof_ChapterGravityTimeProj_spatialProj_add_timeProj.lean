-- Prove2me | Theorems.Thm_BookProof_ChapterGravityTimeProj_spatialProj_add_timeProj
-- name    : BookProof.ChapterGravityTimeProj.spatialProj_add_timeProj
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T11:51:26.941699+00:00
-- url     : https://prove2.me/theorems/d6d692a2-fd3d-426e-aecb-8b1b3d70cbfd
-- title:
--   `BookProof.ChapterGravityTimeProj.spatialProj_add_timeProj` (v : Fin 4 → ℝ) : spatialProj v + timeProj v = 1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGravityTimeProj`.
--
--   `BookProof.ChapterGravityTimeProj.spatialProj_add_timeProj` (v : Fin 4 → ℝ) : spatialProj v + timeProj v = 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGravityTimeProj.spatialProj_add_timeProj`.

-- Generated from ChapterGravityTimeProj.lean — theorem BookProof.ChapterGravityTimeProj.spatialProj_add_timeProj
import Mathlib
import Definitions.Def_ChapterGravityTimeProj
import Definitions.Def_ChapterGravityProjector
open BookProof.ChapterGravityProjector
open BookProof.ChapterGravityTimeProj



open Matrix
open scoped BigOperators
open BookProof.ChapterGravityProjector

theorem BookProof.ChapterGravityTimeProj.spatialProj_add_timeProj (v : Fin 4 → ℝ) :
    spatialProj v + timeProj v = 1 := by sorry
