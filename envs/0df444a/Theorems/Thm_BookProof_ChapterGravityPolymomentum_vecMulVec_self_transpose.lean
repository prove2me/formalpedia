-- Prove2me | Theorems.Thm_BookProof_ChapterGravityPolymomentum_vecMulVec_self_transpose
-- name    : BookProof.ChapterGravityPolymomentum.vecMulVec_self_transpose
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T11:46:06.330985+00:00
-- url     : https://prove2.me/theorems/b528ff6a-2423-4a2d-9d52-de58127adcee
-- title:
--   `BookProof.ChapterGravityPolymomentum.vecMulVec_self_transpose` (v : Fin 4 → ℝ) : (vecMulVec v v)ᵀ = vecMulVec v v
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGravityPolymomentum`.
--
--   `BookProof.ChapterGravityPolymomentum.vecMulVec_self_transpose` (v : Fin 4 → ℝ) : (vecMulVec v v)ᵀ = vecMulVec v v
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGravityPolymomentum.vecMulVec_self_transpose`.

-- Generated from ChapterGravityPolymomentum.lean — theorem BookProof.ChapterGravityPolymomentum.vecMulVec_self_transpose
import Definitions.Def_ChapterGravityProjector
import Mathlib
import Definitions.Def_ChapterGravityPolymomentum
open BookProof.ChapterGravityPolymomentum



open Matrix
open scoped BigOperators
open BookProof.ChapterGravityProjector

theorem BookProof.ChapterGravityPolymomentum.vecMulVec_self_transpose (v : Fin 4 → ℝ) :
    (vecMulVec v v)ᵀ = vecMulVec v v := by sorry
