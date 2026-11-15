-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b24_true_finite_smallnegative_mark_step_increment_le_interval_actual_jump_count
-- name    : AvramDividend.Classical.avram_b24_true_finite_smallnegative_mark_step_increment_le_interval_actual_jump_count
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T18:36:07.246391+00:00
-- url     : https://prove2.me/theorems/57bd9165-a669-4681-827b-544946524634
-- title:
--   A true finite marked negative-smalljump path increment is dominated by actual marked jumps within the physical interval
-- statement:
--   For the right-inclusive chronological finite-step accumulation of genuine negative small Lévy jump marks z(u) in (-1,0), the absolute difference between its values at ordered physical times s≤t is bounded by the ACTUAL number of marked jump times in (s,t]. Each marked contribution in that interval has size strictly less than 1; all jumps at s are already included in the earlier cumulative value and jumps after t are excluded. This preserves the strict-left/inclusive-right convention at ruin, and supplies a marked-source variation bound applicable to finite-activity original Jsmall and stopped physical grids. No stochastic moment assumption on large marks.
-- source:
--   Pinned true finite marked interval filter and finite sum norm/card bound.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b24_true_finite_smallnegative_mark_step_increment_le_interval_actual_jump_count
    (S : Finset ℝ≥0) (z : ℝ≥0 → ℝ)
    (s t : ℝ≥0) (hst : s ≤ t) :
    ‖(∑ u ∈ S,
         if u ≤ t then (if -1 < z u ∧ z u < 0 then z u else 0) else 0) -
      (∑ u ∈ S,
         if u ≤ s then (if -1 < z u ∧ z u < 0 then z u else 0) else 0)‖ ≤
      ((S.filter (fun u => s < u ∧ u ≤ t ∧ -1 < z u ∧ z u < 0)).card : ℝ)
    := by sorry
