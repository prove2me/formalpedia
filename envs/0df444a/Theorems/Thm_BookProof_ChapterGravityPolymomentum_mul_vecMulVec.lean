-- Prove2me | Theorems.Thm_BookProof_ChapterGravityPolymomentum_mul_vecMulVec
-- name    : BookProof.ChapterGravityPolymomentum.mul_vecMulVec
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T13:00:48.521603+00:00
-- url     : https://prove2.me/theorems/4fd7c37d-c3e9-44da-8daf-40727350ed95
-- title:
--   `BookProof.ChapterGravityPolymomentum.mul_vecMulVec` (M : Matrix (Fin 4) (Fin 4) ℝ) (w u : Fin 4 → ℝ) : M * vecMulVec w u = vecMulVec (M.mulVec w) u
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGravityPolymomentum`.
--
--   `BookProof.ChapterGravityPolymomentum.mul_vecMulVec` (M : Matrix (Fin 4) (Fin 4) ℝ) (w u : Fin 4 → ℝ) : M * vecMulVec w u = vecMulVec (M.mulVec w) u
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGravityPolymomentum.mul_vecMulVec`.

-- Generated from ChapterGravityPolymomentum.lean — theorem BookProof.ChapterGravityPolymomentum.mul_vecMulVec
import Definitions.Def_ChapterGravityProjector
import Mathlib
import Definitions.Def_ChapterGravityPolymomentum
open BookProof.ChapterGravityPolymomentum



open Matrix
open scoped BigOperators
open BookProof.ChapterGravityProjector

theorem BookProof.ChapterGravityPolymomentum.mul_vecMulVec (M : Matrix (Fin 4) (Fin 4) ℝ) (w u : Fin 4 → ℝ) :
    M * vecMulVec w u = vecMulVec (M.mulVec w) u := by sorry
