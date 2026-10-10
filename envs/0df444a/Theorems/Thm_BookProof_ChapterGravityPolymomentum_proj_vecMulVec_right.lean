-- Prove2me | Theorems.Thm_BookProof_ChapterGravityPolymomentum_proj_vecMulVec_right
-- name    : BookProof.ChapterGravityPolymomentum.proj_vecMulVec_right
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T11:45:38.678113+00:00
-- url     : https://prove2.me/theorems/ada7ea9d-983c-47ea-a4b2-30db4f14aa80
-- title:
--   `BookProof.ChapterGravityPolymomentum.proj_vecMulVec_right` (v : Fin 4 → ℝ) (hv : minkSq v = -1) (u : Fin 4 → ℝ) : proj v (vecMulVec u v) = 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGravityPolymomentum`.
--
--   `BookProof.ChapterGravityPolymomentum.proj_vecMulVec_right` (v : Fin 4 → ℝ) (hv : minkSq v = -1) (u : Fin 4 → ℝ) : proj v (vecMulVec u v) = 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGravityPolymomentum.proj_vecMulVec_right`.

-- Generated from ChapterGravityPolymomentum.lean — theorem BookProof.ChapterGravityPolymomentum.proj_vecMulVec_right
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

theorem BookProof.ChapterGravityPolymomentum.proj_vecMulVec_right (v : Fin 4 → ℝ) (hv : minkSq v = -1) (u : Fin 4 → ℝ) :
    proj v (vecMulVec u v) = 0 := by sorry
