-- Prove2me | Theorems.Thm_BookProof_ChapterGravityProjector_spatialProj_mulVec_of_orthogonal
-- name    : BookProof.ChapterGravityProjector.spatialProj_mulVec_of_orthogonal
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T11:50:21.069135+00:00
-- url     : https://prove2.me/theorems/01dfc12b-3e9b-4b88-8a9d-cacfc7d84a1b
-- title:
--   `BookProof.ChapterGravityProjector.spatialProj_mulVec_of_orthogonal` (v x : Fin 4 → ℝ) (hx : ∑ a, lower v a * x a = 0) : (spatialProj v).mulVec x = x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGravityProjector`.
--
--   `BookProof.ChapterGravityProjector.spatialProj_mulVec_of_orthogonal` (v x : Fin 4 → ℝ) (hx : ∑ a, lower v a * x a = 0) : (spatialProj v).mulVec x = x
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGravityProjector.spatialProj_mulVec_of_orthogonal`.

-- Generated from ChapterGravityProjector.lean — theorem BookProof.ChapterGravityProjector.spatialProj_mulVec_of_orthogonal
import Mathlib
import Definitions.Def_ChapterGravityProjector
open BookProof.ChapterGravityProjector



open Matrix
open scoped BigOperators

theorem BookProof.ChapterGravityProjector.spatialProj_mulVec_of_orthogonal (v x : Fin 4 → ℝ)
    (hx : ∑ a, lower v a * x a = 0) :
    (spatialProj v).mulVec x = x := by sorry
