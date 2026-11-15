-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a30_single_mark_causal_step_right_continuous_20261114
-- name    : AvramDividend.Classical.avram_a30_single_mark_causal_step_right_continuous_20261114
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T08:19:42.807208+00:00
-- url     : https://prove2.me/theorems/f2664641-27b1-47cd-84b3-1db66b005aa3
-- title:
--   Single marked physical jump causal step is right continuous at all times
-- statement:
--   For every nonnegative marked jump time u and real mark a, the causal jump accumulator step a times the indicator of u≤t is right-continuous at every nonnegative time.
-- source:
--   Pinned Mathlib neighbourhood filters and eventual function equality.

import Mathlib
open Set Filter Topology
open scoped NNReal ENNReal
noncomputable section

/-- A real step contribution of a marked jump is right-continuous at every time. -/

theorem AvramDividend.Classical.avram_a30_single_mark_causal_step_right_continuous_20261114 (u : ℝ≥0) (a : ℝ) :
    ∀ t : ℝ≥0,
      ContinuousWithinAt (fun v : ℝ≥0 => if u ≤ v then a else 0)
        (Ici t) t := by sorry
