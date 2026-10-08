-- Prove2me | Theorems.Thm_BookProof_ChapterGravityPolymomentum_vecMulVec_mul
-- name    : BookProof.ChapterGravityPolymomentum.vecMulVec_mul
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T13:01:47.304958+00:00
-- url     : https://prove2.me/theorems/9dfd12d3-47e8-4521-91a2-b90bb0917f30
-- title:
--   `BookProof.ChapterGravityPolymomentum.vecMulVec_mul` (w u : Fin 4 → ℝ) (M : Matrix (Fin 4) (Fin 4) ℝ) : vecMulVec w u * M = vecMulVec w (M.vecMul u)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGravityPolymomentum`.
--
--   `BookProof.ChapterGravityPolymomentum.vecMulVec_mul` (w u : Fin 4 → ℝ) (M : Matrix (Fin 4) (Fin 4) ℝ) : vecMulVec w u * M = vecMulVec w (M.vecMul u)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGravityPolymomentum.vecMulVec_mul`.

-- Generated from ChapterGravityPolymomentum.lean — theorem BookProof.ChapterGravityPolymomentum.vecMulVec_mul
import Definitions.Def_ChapterGravityProjector
import Mathlib
import Definitions.Def_ChapterGravityPolymomentum
open BookProof.ChapterGravityPolymomentum



open Matrix
open scoped BigOperators
open BookProof.ChapterGravityProjector

theorem BookProof.ChapterGravityPolymomentum.vecMulVec_mul (w u : Fin 4 → ℝ) (M : Matrix (Fin 4) (Fin 4) ℝ) :
    vecMulVec w u * M = vecMulVec w (M.vecMul u) := by sorry
