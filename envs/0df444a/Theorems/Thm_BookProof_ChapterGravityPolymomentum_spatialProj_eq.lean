-- Prove2me | Theorems.Thm_BookProof_ChapterGravityPolymomentum_spatialProj_eq
-- name    : BookProof.ChapterGravityPolymomentum.spatialProj_eq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T13:01:46.480979+00:00
-- url     : https://prove2.me/theorems/53ad969a-eaf6-40a4-b142-c498a58f2781
-- title:
--   `BookProof.ChapterGravityPolymomentum.spatialProj_eq` (v : Fin 4 → ℝ) : spatialProj v = 1 + vecMulVec v (lower v)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGravityPolymomentum`.
--
--   `BookProof.ChapterGravityPolymomentum.spatialProj_eq` (v : Fin 4 → ℝ) : spatialProj v = 1 + vecMulVec v (lower v)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGravityPolymomentum.spatialProj_eq`.

-- Generated from ChapterGravityPolymomentum.lean — theorem BookProof.ChapterGravityPolymomentum.spatialProj_eq
import Mathlib
import Definitions.Def_ChapterGravityPolymomentum
import Definitions.Def_ChapterGravityProjector
open BookProof.ChapterGravityProjector
open BookProof.ChapterGravityPolymomentum



open Matrix
open scoped BigOperators
open BookProof.ChapterGravityProjector

theorem BookProof.ChapterGravityPolymomentum.spatialProj_eq (v : Fin 4 → ℝ) : spatialProj v = 1 + vecMulVec v (lower v) := by sorry
