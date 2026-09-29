-- Prove2me | Theorems.Thm_BookProof_ChapterH6_sirk_error_decay_exponential
-- name    : BookProof.ChapterH6.sirk_error_decay_exponential
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T04:21:30.347231+00:00
-- url     : https://prove2.me/theorems/2c9e11b4-d94f-4ce1-8077-1ab26a5ae1a8
-- title:
--   (C Dmin h nv : ℝ) (hh : 0 < h) : Tendsto (fun m : ℕ => sirkBound C Dmin h nv m) atTop (𝓝 0)
-- statement:
--   Lean 4 theorem `BookProof.ChapterH6.sirk_error_decay_exponential` (module `BookProof.ChapterH6`), source chapter `BookProof/ChapterChapterH6.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterH6.lean

-- Generated from ChapterH6.lean — theorem BookProof.ChapterH6.sirk_error_decay_exponential
import Mathlib
import Definitions.Def_ChapterH6
open BookProof.ChapterH6
open Filter Topology

set_option maxHeartbeats 1000000 in

theorem BookProof.ChapterH6.sirk_error_decay_exponential (C Dmin h nv : ℝ) (hh : 0 < h) :
    Tendsto (fun m : ℕ => sirkBound C Dmin h nv m) atTop (𝓝 0) := by sorry
