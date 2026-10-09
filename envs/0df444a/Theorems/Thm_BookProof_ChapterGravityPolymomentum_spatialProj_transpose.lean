-- Prove2me | Theorems.Thm_BookProof_ChapterGravityPolymomentum_spatialProj_transpose
-- name    : BookProof.ChapterGravityPolymomentum.spatialProj_transpose
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T13:02:40.92318+00:00
-- url     : https://prove2.me/theorems/13438a73-2f60-4716-925b-1d1e9a2e33bd
-- title:
--   `BookProof.ChapterGravityPolymomentum.spatialProj_transpose` (v : Fin 4 → ℝ) : (spatialProj v)ᵀ = 1 + vecMulVec (lower v) v
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGravityPolymomentum`.
--
--   `BookProof.ChapterGravityPolymomentum.spatialProj_transpose` (v : Fin 4 → ℝ) : (spatialProj v)ᵀ = 1 + vecMulVec (lower v) v
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGravityPolymomentum.spatialProj_transpose`.

-- Generated from ChapterGravityPolymomentum.lean — theorem BookProof.ChapterGravityPolymomentum.spatialProj_transpose
import Mathlib
import Definitions.Def_ChapterGravityPolymomentum
import Definitions.Def_ChapterGravityProjector
open BookProof.ChapterGravityProjector
open BookProof.ChapterGravityPolymomentum



open Matrix
open scoped BigOperators
open BookProof.ChapterGravityProjector

theorem BookProof.ChapterGravityPolymomentum.spatialProj_transpose (v : Fin 4 → ℝ) :
    (spatialProj v)ᵀ = 1 + vecMulVec (lower v) v := by sorry
