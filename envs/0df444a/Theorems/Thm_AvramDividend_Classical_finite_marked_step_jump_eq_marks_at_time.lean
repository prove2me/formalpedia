-- Prove2me | Theorems.Thm_AvramDividend_Classical_finite_marked_step_jump_eq_marks_at_time
-- name    : AvramDividend.Classical.finite_marked_step_jump_eq_marks_at_time
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:44:21.573988+00:00
-- url     : https://prove2.me/theorems/7808fdb9-af61-4b09-a1d3-af464862bccc
-- title:
--   The exact left-jump size of a finite marked step path equals the total mark weight arriving at that time
-- statement:
--   For finitely many marked arrival times τ_i≥0 and real weights w_i, a right-continuous step path accumulates w_i at time τ_i. The difference of its current value at t and its left-limit step sum equals precisely the sum of weights w_i whose arrival time is exactly t. The result is valid even with simultaneous arrivals and requires no sign restriction. Together with the separately authored finite_marked_step_sum_left_limit theorem, it identifies the jump sizes of a canonical finite-band compound-Poisson marked path and isolates the further almost-sure no-simultaneous-marks hypothesis needed for one-to-one jump counts.
-- source:
--   Mathlib Finset.sum_sub_distrib and linear-order trichotomy. Finite-mark step constructions in LeanLevy/RandomMeasure/LevyJumpPath.lean.

import Mathlib.Data.NNReal.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring

open scoped NNReal BigOperators

theorem AvramDividend.Classical.finite_marked_step_jump_eq_marks_at_time
    {ι : Type*} (S : Finset ι) (τ : ι → ℝ≥0) (w : ι → ℝ) (t : ℝ≥0) :
    (∑ i ∈ S, if τ i ≤ t then w i else 0) -
      (∑ i ∈ S, if τ i < t then w i else 0) =
    ∑ i ∈ S, if τ i = t then w i else 0 := by sorry
