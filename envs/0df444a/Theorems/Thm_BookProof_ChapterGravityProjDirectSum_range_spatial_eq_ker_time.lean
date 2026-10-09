-- Prove2me | Theorems.Thm_BookProof_ChapterGravityProjDirectSum_range_spatial_eq_ker_time
-- name    : BookProof.ChapterGravityProjDirectSum.range_spatial_eq_ker_time
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T11:49:26.982302+00:00
-- url     : https://prove2.me/theorems/302da943-dee3-4ded-9b9a-ba8b3c21beb8
-- title:
--   `BookProof.ChapterGravityProjDirectSum.range_spatial_eq_ker_time` (v : Fin 4 → ℝ) (hv : minkSq v = -1) : LinearMap.range (spatialProj v).mulVecLin = LinearMap.ker (timeProj v).mulV
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGravityProjDirectSum`.
--
--   `BookProof.ChapterGravityProjDirectSum.range_spatial_eq_ker_time` (v : Fin 4 → ℝ) (hv : minkSq v = -1) : LinearMap.range (spatialProj v).mulVecLin = LinearMap.ker (timeProj v).mulVecLin
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGravityProjDirectSum.range_spatial_eq_ker_time`.

-- Generated from ChapterGravityProjDirectSum.lean — theorem BookProof.ChapterGravityProjDirectSum.range_spatial_eq_ker_time
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

theorem BookProof.ChapterGravityProjDirectSum.range_spatial_eq_ker_time (v : Fin 4 → ℝ) (hv : minkSq v = -1) :
    LinearMap.range (spatialProj v).mulVecLin
      = LinearMap.ker (timeProj v).mulVecLin := by sorry
