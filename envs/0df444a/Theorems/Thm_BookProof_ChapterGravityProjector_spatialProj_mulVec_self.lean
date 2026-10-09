-- Prove2me | Theorems.Thm_BookProof_ChapterGravityProjector_spatialProj_mulVec_self
-- name    : BookProof.ChapterGravityProjector.spatialProj_mulVec_self
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T11:49:28.253762+00:00
-- url     : https://prove2.me/theorems/2a8b9bdf-6628-481e-a574-09f36862ac6d
-- title:
--   `BookProof.ChapterGravityProjector.spatialProj_mulVec_self` (v : Fin 4 → ℝ) (hv : minkSq v = -1) : (spatialProj v).mulVec v = 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGravityProjector`.
--
--   `BookProof.ChapterGravityProjector.spatialProj_mulVec_self` (v : Fin 4 → ℝ) (hv : minkSq v = -1) : (spatialProj v).mulVec v = 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGravityProjector.spatialProj_mulVec_self`.

-- Generated from ChapterGravityProjector.lean — theorem BookProof.ChapterGravityProjector.spatialProj_mulVec_self
import Mathlib
import Definitions.Def_ChapterGravityProjector
open BookProof.ChapterGravityProjector



open Matrix
open scoped BigOperators

theorem BookProof.ChapterGravityProjector.spatialProj_mulVec_self (v : Fin 4 → ℝ) (hv : minkSq v = -1) :
    (spatialProj v).mulVec v = 0 := by sorry
