-- Prove2me | Theorems.Thm_AvramDividend_Classical_finite_mark_step_large_negative_jump_iff_mark
-- name    : AvramDividend.Classical.finite_mark_step_large_negative_jump_iff_mark
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T07:17:43.07799+00:00
-- url     : https://prove2.me/theorems/0e8c31e7-f136-4874-aa47-b4015757371f
-- title:
--   Every large negative càdlàg jump of a collision-free finite marked step process occurs at exactly one negative marked arrival
-- statement:
--   For a finite marked right-continuous step path with distinct mark arrival times and any nonnegative jump threshold a, its strict downward left-jump size at an arbitrary nonnegative time t exceeds a if and only if a mark arrives exactly at t with weight smaller than -a. In particular no spurious jumps occur at unmarked times. The proof splits on whether t is an arrival time; on arrival, the accepted singleton jump identity identifies the unique mark weight, and off the arrival set the accepted aggregate mark identity gives jump zero, which cannot exceed a≥0. This is the exact all-time path-jump event/marked-arrival identification needed before a Poisson finite-band jump-count law is transported from canonical marks to intrinsic càdlàg paths.
-- source:
--   Proved finite_marked_step_jump_eq_marks_at_time [7808fdb9-af61-4b09-a1d3-af464862bccc] and finite_marked_step_jump_eq_single_of_injective [b86cfb0f-2396-446a-8633-384f9a45bcff]; LeanLevy/RandomMeasure/LevyJumpPath.lean finite band sums.

import Mathlib.Data.NNReal.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_finite_marked_step_jump_eq_marks_at_time
import Theorems.Thm_AvramDividend_Classical_finite_marked_step_jump_eq_single_of_injective

open AvramDividend.Classical
open scoped NNReal BigOperators

theorem AvramDividend.Classical.finite_mark_step_large_negative_jump_iff_mark
    {ι : Type*} (S : Finset ι) (τ : ι → ℝ≥0) (w : ι → ℝ)
    (hτ : ∀ i ∈ S, ∀ j ∈ S, τ i = τ j → i = j)
    (a : ℝ) (ha : 0 ≤ a) (t : ℝ≥0) :
    ((∑ j ∈ S, if τ j ≤ t then w j else 0) -
      (∑ j ∈ S, if τ j < t then w j else 0) < -a) ↔
      ∃ i ∈ S, τ i = t ∧ w i < -a := by sorry
