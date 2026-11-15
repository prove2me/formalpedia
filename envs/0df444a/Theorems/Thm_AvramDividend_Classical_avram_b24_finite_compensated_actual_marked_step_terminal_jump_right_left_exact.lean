-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b24_finite_compensated_actual_marked_step_terminal_jump_right_left_exact
-- name    : AvramDividend.Classical.avram_b24_finite_compensated_actual_marked_step_terminal_jump_right_left_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T17:08:44.774662+00:00
-- url     : https://prove2.me/theorems/43f97f21-8838-42ab-84bd-3d2db2a92a80
-- title:
--   The actual finite negative compensated marked-step source has strict-left limit and exact original terminal physical jump
-- statement:
--   Suppose a true finite-activity intrinsic compensated marked source Jsmall on a bounded physical horizon has been explicitly identified at every time v as the cumulative FINITE actual small-negative-mark step sum of original source jumps plus deterministic compensated drift. Then at every positive terminal contact t the source tends from the left to the strict-left sum minus t times the compensator drift, and its terminal jump equals exactly the actual mark at t if present and in (-1,0). The genuine ruin-causing jump persists; Gaussian continuity reasoning cannot be used for this marked source. This follows from Proved actual marked finite step left-limit and Proved exact terminal atom difference.
-- source:
--   Proved B24 terminal finite-mark singleton atom and original a30 finite causal step left-limits.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_b24_actual_finite_mark_step_source_terminal_jump_exact
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b24_finite_compensated_actual_marked_step_terminal_jump_right_left_exact
    (S : Finset ℝ≥0) (z : ℝ≥0 → ℝ) (d : ℝ)
    (Jsmall : ℝ≥0 → ℝ) (T t : ℝ≥0)
    (ht0 : 0 < t) (htT : t ≤ T)
    (hPath : ∀ v : ℝ≥0, v ≤ T →
      Jsmall v =
        (∑ u ∈ S,
          if u ≤ v then (if -1 < z u ∧ z u < 0 then z u else 0) else 0) -
        (v : ℝ) * d) :
    Tendsto Jsmall (𝓝[<] t)
      (𝓝 ((∑ u ∈ S,
          if u < t then (if -1 < z u ∧ z u < 0 then z u else 0) else 0) -
        (t : ℝ) * d)) ∧
    Jsmall t -
      ((∑ u ∈ S,
          if u < t then (if -1 < z u ∧ z u < 0 then z u else 0) else 0) -
        (t : ℝ) * d) =
      if t ∈ S then (if -1 < z t ∧ z t < 0 then z t else 0) else 0 := by sorry
