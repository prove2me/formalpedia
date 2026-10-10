-- Prove2me | Theorems.Thm_BookProof_ChapterGravityProjector_spatialProj_idempotent
-- name    : BookProof.ChapterGravityProjector.spatialProj_idempotent
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T11:49:47.886644+00:00
-- url     : https://prove2.me/theorems/b736cfa6-accb-40f7-9b25-4114c19ce5db
-- title:
--   `BookProof.ChapterGravityProjector.spatialProj_idempotent` (v : Fin 4 → ℝ) (hv : minkSq v = -1) : spatialProj v * spatialProj v = spatialProj v
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGravityProjector`.
--
--   `BookProof.ChapterGravityProjector.spatialProj_idempotent` (v : Fin 4 → ℝ) (hv : minkSq v = -1) : spatialProj v * spatialProj v = spatialProj v
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGravityProjector.spatialProj_idempotent`.

-- Generated from ChapterGravityProjector.lean — theorem BookProof.ChapterGravityProjector.spatialProj_idempotent
import Mathlib
import Definitions.Def_ChapterGravityProjector
open BookProof.ChapterGravityProjector



open Matrix
open scoped BigOperators

theorem BookProof.ChapterGravityProjector.spatialProj_idempotent (v : Fin 4 → ℝ) (hv : minkSq v = -1) :
    spatialProj v * spatialProj v = spatialProj v := by sorry
