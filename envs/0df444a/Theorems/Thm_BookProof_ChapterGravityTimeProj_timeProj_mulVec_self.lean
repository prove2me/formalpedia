-- Prove2me | Theorems.Thm_BookProof_ChapterGravityTimeProj_timeProj_mulVec_self
-- name    : BookProof.ChapterGravityTimeProj.timeProj_mulVec_self
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T11:52:22.250974+00:00
-- url     : https://prove2.me/theorems/8afa1e84-4fe4-4ff7-957c-6f00eb5b9833
-- title:
--   `BookProof.ChapterGravityTimeProj.timeProj_mulVec_self` (v : Fin 4 → ℝ) (hv : minkSq v = -1) : (timeProj v).mulVec v = v
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGravityTimeProj`.
--
--   `BookProof.ChapterGravityTimeProj.timeProj_mulVec_self` (v : Fin 4 → ℝ) (hv : minkSq v = -1) : (timeProj v).mulVec v = v
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGravityTimeProj.timeProj_mulVec_self`.

-- Generated from ChapterGravityTimeProj.lean — theorem BookProof.ChapterGravityTimeProj.timeProj_mulVec_self
import Mathlib
import Definitions.Def_ChapterGravityTimeProj
import Definitions.Def_ChapterGravityProjector
open BookProof.ChapterGravityProjector
open BookProof.ChapterGravityTimeProj



open Matrix
open scoped BigOperators
open BookProof.ChapterGravityProjector

theorem BookProof.ChapterGravityTimeProj.timeProj_mulVec_self (v : Fin 4 → ℝ) (hv : minkSq v = -1) :
    (timeProj v).mulVec v = v := by sorry
