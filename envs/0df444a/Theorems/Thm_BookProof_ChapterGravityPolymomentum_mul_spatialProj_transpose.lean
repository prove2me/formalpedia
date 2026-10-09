-- Prove2me | Theorems.Thm_BookProof_ChapterGravityPolymomentum_mul_spatialProj_transpose
-- name    : BookProof.ChapterGravityPolymomentum.mul_spatialProj_transpose
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T13:04:43.150735+00:00
-- url     : https://prove2.me/theorems/25d13402-c389-414f-9d2f-0b187aa13506
-- title:
--   `BookProof.ChapterGravityPolymomentum.mul_spatialProj_transpose` (v : Fin 4 → ℝ) (M : Matrix (Fin 4) (Fin 4) ℝ) : M * (spatialProj v)ᵀ = M + vecMulVec (M.mulVec (lower v)) v
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGravityPolymomentum`.
--
--   `BookProof.ChapterGravityPolymomentum.mul_spatialProj_transpose` (v : Fin 4 → ℝ) (M : Matrix (Fin 4) (Fin 4) ℝ) : M * (spatialProj v)ᵀ = M + vecMulVec (M.mulVec (lower v)) v
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGravityPolymomentum.mul_spatialProj_transpose`.

-- Generated from ChapterGravityPolymomentum.lean — theorem BookProof.ChapterGravityPolymomentum.mul_spatialProj_transpose
import Mathlib
import Definitions.Def_ChapterGravityPolymomentum
import Definitions.Def_ChapterGravityProjector
open BookProof.ChapterGravityProjector
open BookProof.ChapterGravityPolymomentum



open Matrix
open scoped BigOperators
open BookProof.ChapterGravityProjector

theorem BookProof.ChapterGravityPolymomentum.mul_spatialProj_transpose (v : Fin 4 → ℝ) (M : Matrix (Fin 4) (Fin 4) ℝ) :
    M * (spatialProj v)ᵀ = M + vecMulVec (M.mulVec (lower v)) v := by sorry
