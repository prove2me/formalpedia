-- Prove2me | Theorems.Thm_BookProof_ChapterGravityProjDirectSum_isCompl_spatial_time_range
-- name    : BookProof.ChapterGravityProjDirectSum.isCompl_spatial_time_range
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T11:49:26.296973+00:00
-- url     : https://prove2.me/theorems/d252bf84-03c6-4fea-bb1f-8631131f8252
-- title:
--   `BookProof.ChapterGravityProjDirectSum.isCompl_spatial_time_range` (v : Fin 4 → ℝ) (hv : minkSq v = -1) : IsCompl (LinearMap.range (spatialProj v).mulVecLin) (LinearMap.range (time
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGravityProjDirectSum`.
--
--   `BookProof.ChapterGravityProjDirectSum.isCompl_spatial_time_range` (v : Fin 4 → ℝ) (hv : minkSq v = -1) : IsCompl (LinearMap.range (spatialProj v).mulVecLin) (LinearMap.range (timeProj v).mulVecLin)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGravityProjDirectSum.isCompl_spatial_time_range`.

-- Generated from ChapterGravityProjDirectSum.lean — theorem BookProof.ChapterGravityProjDirectSum.isCompl_spatial_time_range
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

theorem BookProof.ChapterGravityProjDirectSum.isCompl_spatial_time_range (v : Fin 4 → ℝ) (hv : minkSq v = -1) :
    IsCompl (LinearMap.range (spatialProj v).mulVecLin)
      (LinearMap.range (timeProj v).mulVecLin) := by sorry
