-- Prove2me | Theorems.Thm_BookProof_ChapterGravityProjDirectSum_mulVecLin_spatial_comp_time
-- name    : BookProof.ChapterGravityProjDirectSum.mulVecLin_spatial_comp_time
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T11:49:14.492124+00:00
-- url     : https://prove2.me/theorems/76dbc860-a38b-4684-a5cd-e42dabb071f1
-- title:
--   `BookProof.ChapterGravityProjDirectSum.mulVecLin_spatial_comp_time` (v : Fin 4 → ℝ) (hv : minkSq v = -1) : (spatialProj v).mulVecLin.comp (timeProj v).mulVecLin = 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGravityProjDirectSum`.
--
--   `BookProof.ChapterGravityProjDirectSum.mulVecLin_spatial_comp_time` (v : Fin 4 → ℝ) (hv : minkSq v = -1) : (spatialProj v).mulVecLin.comp (timeProj v).mulVecLin = 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGravityProjDirectSum.mulVecLin_spatial_comp_time`.

-- Generated from ChapterGravityProjDirectSum.lean — theorem BookProof.ChapterGravityProjDirectSum.mulVecLin_spatial_comp_time
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

theorem BookProof.ChapterGravityProjDirectSum.mulVecLin_spatial_comp_time (v : Fin 4 → ℝ) (hv : minkSq v = -1) :
    (spatialProj v).mulVecLin.comp (timeProj v).mulVecLin = 0 := by sorry
