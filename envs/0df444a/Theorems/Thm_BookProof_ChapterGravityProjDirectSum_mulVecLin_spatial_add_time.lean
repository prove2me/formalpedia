-- Prove2me | Theorems.Thm_BookProof_ChapterGravityProjDirectSum_mulVecLin_spatial_add_time
-- name    : BookProof.ChapterGravityProjDirectSum.mulVecLin_spatial_add_time
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T11:48:46.610185+00:00
-- url     : https://prove2.me/theorems/1cae5333-54f4-4e76-a98a-e7d88c7e4970
-- title:
--   `BookProof.ChapterGravityProjDirectSum.mulVecLin_spatial_add_time` (v : Fin 4 → ℝ) : (spatialProj v).mulVecLin + (timeProj v).mulVecLin = LinearMap.id
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGravityProjDirectSum`.
--
--   `BookProof.ChapterGravityProjDirectSum.mulVecLin_spatial_add_time` (v : Fin 4 → ℝ) : (spatialProj v).mulVecLin + (timeProj v).mulVecLin = LinearMap.id
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGravityProjDirectSum.mulVecLin_spatial_add_time`.

-- Generated from ChapterGravityProjDirectSum.lean — theorem BookProof.ChapterGravityProjDirectSum.mulVecLin_spatial_add_time
import Mathlib
import Definitions.Def_ChapterGravityProjDirectSum
import Definitions.Def_ChapterGravityProjector
import Definitions.Def_ChapterGravityTimeProj
open BookProof.ChapterGravityProjector
open BookProof.ChapterGravityTimeProj
open BookProof.ChapterGravityProjDirectSum


open Matrix


open BookProof.ChapterGravityProjector
open BookProof.ChapterGravityTimeProj

theorem BookProof.ChapterGravityProjDirectSum.mulVecLin_spatial_add_time (v : Fin 4 → ℝ) :
    (spatialProj v).mulVecLin + (timeProj v).mulVecLin = LinearMap.id := by sorry
