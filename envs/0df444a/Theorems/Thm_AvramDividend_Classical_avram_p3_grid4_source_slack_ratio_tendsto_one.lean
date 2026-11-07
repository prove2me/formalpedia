-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_source_slack_ratio_tendsto_one
-- name    : AvramDividend.Classical.avram_p3_grid4_source_slack_ratio_tendsto_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T06:38:37.28303+00:00
-- url     : https://prove2.me/theorems/d25caef8-65bc-49db-be9d-e63e30a31ee3
-- title:
--   Vanishing source slack yields an extended-real discount factor converging to one
-- statement:
--   This repairs missing ENNReal scoped notation in v1, preserving full original statement. Real division continuity at a nonzero positive benchmark, followed by ENNReal.ofReal continuity, gives the source slack discount tending to one.

import Mathlib
open Filter
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid4_source_slack_ratio_tendsto_one
    (w : ℝ) (hw : 0 < w) (e : ℕ → ℝ)
    (he : Filter.Tendsto e Filter.atTop (nhds (0 : ℝ))) :
    Filter.Tendsto (fun n => ENNReal.ofReal (w / (w + e n)))
      Filter.atTop (nhds (1 : ℝ≥0∞)) := by sorry
