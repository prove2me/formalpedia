-- Prove2me | Theorems.Thm_BookProof_ChapterGravityProjector_trace_spatialProj
-- name    : BookProof.ChapterGravityProjector.trace_spatialProj
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T11:50:00.232327+00:00
-- url     : https://prove2.me/theorems/98a6c0da-4dc8-4049-9f1a-1564da07ddad
-- title:
--   `BookProof.ChapterGravityProjector.trace_spatialProj` (v : Fin 4 → ℝ) (hv : minkSq v = -1) : (spatialProj v).trace = 3
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGravityProjector`.
--
--   `BookProof.ChapterGravityProjector.trace_spatialProj` (v : Fin 4 → ℝ) (hv : minkSq v = -1) : (spatialProj v).trace = 3
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGravityProjector.trace_spatialProj`.

-- Generated from ChapterGravityProjector.lean — theorem BookProof.ChapterGravityProjector.trace_spatialProj
import Mathlib
import Definitions.Def_ChapterGravityProjector
open BookProof.ChapterGravityProjector



open Matrix
open scoped BigOperators

theorem BookProof.ChapterGravityProjector.trace_spatialProj (v : Fin 4 → ℝ) (hv : minkSq v = -1) :
    (spatialProj v).trace = 3 := by sorry
