-- Prove2me | Theorems.Thm_BookProof_ChapterGravityTimeProj_timeProj_idempotent
-- name    : BookProof.ChapterGravityTimeProj.timeProj_idempotent
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T11:52:02.917991+00:00
-- url     : https://prove2.me/theorems/291ace6f-3816-4553-9eca-0e034d2bdfb5
-- title:
--   `BookProof.ChapterGravityTimeProj.timeProj_idempotent` (v : Fin 4 → ℝ) (hv : minkSq v = -1) : timeProj v * timeProj v = timeProj v
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGravityTimeProj`.
--
--   `BookProof.ChapterGravityTimeProj.timeProj_idempotent` (v : Fin 4 → ℝ) (hv : minkSq v = -1) : timeProj v * timeProj v = timeProj v
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGravityTimeProj.timeProj_idempotent`.

-- Generated from ChapterGravityTimeProj.lean — theorem BookProof.ChapterGravityTimeProj.timeProj_idempotent
import Mathlib
import Definitions.Def_ChapterGravityTimeProj
import Definitions.Def_ChapterGravityProjector
open BookProof.ChapterGravityProjector
open BookProof.ChapterGravityTimeProj



open Matrix
open scoped BigOperators
open BookProof.ChapterGravityProjector

theorem BookProof.ChapterGravityTimeProj.timeProj_idempotent (v : Fin 4 → ℝ) (hv : minkSq v = -1) :
    timeProj v * timeProj v = timeProj v := by sorry
