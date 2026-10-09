-- Prove2me | Theorems.Thm_BookProof_ChapterGravityProjDirectSum_mulVecLin_time_comp_spatial
-- name    : BookProof.ChapterGravityProjDirectSum.mulVecLin_time_comp_spatial
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T11:49:18.623251+00:00
-- url     : https://prove2.me/theorems/1a02cbce-4e2e-4dd8-bfdc-4c3a0863e41e
-- title:
--   `BookProof.ChapterGravityProjDirectSum.mulVecLin_time_comp_spatial` (v : Fin 4 → ℝ) (hv : minkSq v = -1) : (timeProj v).mulVecLin.comp (spatialProj v).mulVecLin = 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGravityProjDirectSum`.
--
--   `BookProof.ChapterGravityProjDirectSum.mulVecLin_time_comp_spatial` (v : Fin 4 → ℝ) (hv : minkSq v = -1) : (timeProj v).mulVecLin.comp (spatialProj v).mulVecLin = 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGravityProjDirectSum.mulVecLin_time_comp_spatial`.

-- Generated from ChapterGravityProjDirectSum.lean — theorem BookProof.ChapterGravityProjDirectSum.mulVecLin_time_comp_spatial
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

theorem BookProof.ChapterGravityProjDirectSum.mulVecLin_time_comp_spatial (v : Fin 4 → ℝ) (hv : minkSq v = -1) :
    (timeProj v).mulVecLin.comp (spatialProj v).mulVecLin = 0 := by sorry
