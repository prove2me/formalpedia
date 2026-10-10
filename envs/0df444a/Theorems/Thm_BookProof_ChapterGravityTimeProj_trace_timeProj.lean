-- Prove2me | Theorems.Thm_BookProof_ChapterGravityTimeProj_trace_timeProj
-- name    : BookProof.ChapterGravityTimeProj.trace_timeProj
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T11:52:04.104286+00:00
-- url     : https://prove2.me/theorems/53aa99fd-fea8-4c9f-a452-1d3ea89b66e3
-- title:
--   `BookProof.ChapterGravityTimeProj.trace_timeProj` (v : Fin 4 → ℝ) (hv : minkSq v = -1) : (timeProj v).trace = 1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGravityTimeProj`.
--
--   `BookProof.ChapterGravityTimeProj.trace_timeProj` (v : Fin 4 → ℝ) (hv : minkSq v = -1) : (timeProj v).trace = 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGravityTimeProj.trace_timeProj`.

-- Generated from ChapterGravityTimeProj.lean — theorem BookProof.ChapterGravityTimeProj.trace_timeProj
import Mathlib
import Definitions.Def_ChapterGravityTimeProj
import Definitions.Def_ChapterGravityProjector
open BookProof.ChapterGravityProjector
open BookProof.ChapterGravityTimeProj



open Matrix
open scoped BigOperators
open BookProof.ChapterGravityProjector

theorem BookProof.ChapterGravityTimeProj.trace_timeProj (v : Fin 4 → ℝ) (hv : minkSq v = -1) :
    (timeProj v).trace = 1 := by sorry
