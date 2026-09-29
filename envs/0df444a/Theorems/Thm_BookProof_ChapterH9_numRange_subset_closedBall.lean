-- Prove2me | Theorems.Thm_BookProof_ChapterH9_numRange_subset_closedBall
-- name    : BookProof.ChapterH9.numRange_subset_closedBall
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T04:23:22.525055+00:00
-- url     : https://prove2.me/theorems/c3533ba1-86c8-4c90-b53c-45c52dfb2b4c
-- title:
--   (X : E →L[ℂ] E) : numRange X ⊆ Metric.closedBall (0 : ℂ) ‖X‖
-- statement:
--   Lean 4 theorem `BookProof.ChapterH9.numRange_subset_closedBall` (module `BookProof.ChapterH9`), source chapter `BookProof/ChapterChapterH9.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterH9.lean

-- Generated from ChapterH9.lean — theorem BookProof.ChapterH9.numRange_subset_closedBall
import Mathlib
import Definitions.Def_ChapterH9
open BookProof.ChapterH9

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]

set_option maxHeartbeats 1000000 in

theorem BookProof.ChapterH9.numRange_subset_closedBall (X : E →L[ℂ] E) :
    numRange X ⊆ Metric.closedBall (0 : ℂ) ‖X‖ := by sorry
