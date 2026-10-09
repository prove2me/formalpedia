-- Prove2me | Theorems.Thm_BookProof_ChapterGravityPolymomentum_spatialMetric_transpose
-- name    : BookProof.ChapterGravityPolymomentum.spatialMetric_transpose
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T11:46:15.227369+00:00
-- url     : https://prove2.me/theorems/3ba8accd-806a-4b3d-ac1d-0d38281917bc
-- title:
--   `BookProof.ChapterGravityPolymomentum.spatialMetric_transpose` (v : Fin 4 → ℝ) : (metric + vecMulVec v v)ᵀ = metric + vecMulVec v v
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGravityPolymomentum`.
--
--   `BookProof.ChapterGravityPolymomentum.spatialMetric_transpose` (v : Fin 4 → ℝ) : (metric + vecMulVec v v)ᵀ = metric + vecMulVec v v
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGravityPolymomentum.spatialMetric_transpose`.

-- Generated from ChapterGravityPolymomentum.lean — theorem BookProof.ChapterGravityPolymomentum.spatialMetric_transpose
import Mathlib
import Definitions.Def_ChapterGravityPolymomentum
import Definitions.Def_ChapterGravityProjector
open BookProof.ChapterGravityProjector
open BookProof.ChapterGravityPolymomentum



open Matrix
open scoped BigOperators
open BookProof.ChapterGravityProjector

theorem BookProof.ChapterGravityPolymomentum.spatialMetric_transpose (v : Fin 4 → ℝ) :
    (metric + vecMulVec v v)ᵀ = metric + vecMulVec v v := by sorry
