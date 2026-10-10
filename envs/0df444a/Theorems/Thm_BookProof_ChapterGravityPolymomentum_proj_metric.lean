-- Prove2me | Theorems.Thm_BookProof_ChapterGravityPolymomentum_proj_metric
-- name    : BookProof.ChapterGravityPolymomentum.proj_metric
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T11:46:12.26349+00:00
-- url     : https://prove2.me/theorems/99f7ca64-07b8-4171-bed1-da22bcf8818c
-- title:
--   `BookProof.ChapterGravityPolymomentum.proj_metric` (v : Fin 4 → ℝ) (hv : minkSq v = -1) : proj v metric = metric + vecMulVec v v
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGravityPolymomentum`.
--
--   `BookProof.ChapterGravityPolymomentum.proj_metric` (v : Fin 4 → ℝ) (hv : minkSq v = -1) : proj v metric = metric + vecMulVec v v
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGravityPolymomentum.proj_metric`.

-- Generated from ChapterGravityPolymomentum.lean — theorem BookProof.ChapterGravityPolymomentum.proj_metric
import Mathlib
import Definitions.Def_ChapterGravityPolymomentum
import Definitions.Def_ChapterElectroweakFieldStrength
import Definitions.Def_ChapterGravityProjector
open BookProof.ChapterElectroweakFieldStrength
open BookProof.ChapterGravityProjector
open BookProof.ChapterGravityPolymomentum



open Matrix
open scoped BigOperators
open BookProof.ChapterGravityProjector

theorem BookProof.ChapterGravityPolymomentum.proj_metric (v : Fin 4 → ℝ) (hv : minkSq v = -1) :
    proj v metric = metric + vecMulVec v v := by sorry
