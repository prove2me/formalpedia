-- Prove2me | Theorems.Thm_BookProof_ChapterGravityPolymomentum_spatialProj_mul
-- name    : BookProof.ChapterGravityPolymomentum.spatialProj_mul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T13:01:52.995749+00:00
-- url     : https://prove2.me/theorems/c8f695d3-689e-4f39-9c3c-f549a70e407d
-- title:
--   `BookProof.ChapterGravityPolymomentum.spatialProj_mul` (v : Fin 4 → ℝ) (M : Matrix (Fin 4) (Fin 4) ℝ) : spatialProj v * M = M + vecMulVec v (M.vecMul (lower v))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGravityPolymomentum`.
--
--   `BookProof.ChapterGravityPolymomentum.spatialProj_mul` (v : Fin 4 → ℝ) (M : Matrix (Fin 4) (Fin 4) ℝ) : spatialProj v * M = M + vecMulVec v (M.vecMul (lower v))
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGravityPolymomentum.spatialProj_mul`.

-- Generated from ChapterGravityPolymomentum.lean — theorem BookProof.ChapterGravityPolymomentum.spatialProj_mul
import Mathlib
import Definitions.Def_ChapterGravityPolymomentum
import Definitions.Def_ChapterGravityProjector
open BookProof.ChapterGravityProjector
open BookProof.ChapterGravityPolymomentum



open Matrix
open scoped BigOperators
open BookProof.ChapterGravityProjector

theorem BookProof.ChapterGravityPolymomentum.spatialProj_mul (v : Fin 4 → ℝ) (M : Matrix (Fin 4) (Fin 4) ℝ) :
    spatialProj v * M = M + vecMulVec v (M.vecMul (lower v)) := by sorry
