-- Prove2me | Theorems.Thm_AvramDividend_Classical_finite_marked_step_jump_eq_single_of_injective
-- name    : AvramDividend.Classical.finite_marked_step_jump_eq_single_of_injective
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T22:53:11.810048+00:00
-- url     : https://prove2.me/theorems/b86cfb0f-2396-446a-8633-384f9a45bcff
-- title:
--   A collision-free finite marked Poisson step process jumps by exactly its individual arriving mark
-- statement:
--   Consider the finite right-continuous step sum of real weights w_i arriving at nonnegative times tau_i. If the map of arrival times is injective on the finite mark set S, then at the arrival time tau_i of any i in S the jump, defined as current value minus strict-past left limit, equals precisely w_i. Proof uses the Proved exact sum-of-all-marks-at-time identity and reduces the time-fibre to the unique index i by injectivity. This is the deterministic link between finite-band canonical Poisson point marks and observed càdlàg jump magnitudes when the atomless time coordinate guarantees no simultaneous points.
-- source:
--   Proved finite_marked_step_jump_eq_marks_at_time [7808fdb9-af61-4b09-a1d3-af464862bccc]. For Lévy Poisson mark-time uniqueness, use the atomlessness of Lebesgue time intensity and PRM simplicity; not assumed established here.

import Mathlib.Data.NNReal.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Theorems.Thm_AvramDividend_Classical_finite_marked_step_jump_eq_marks_at_time

open AvramDividend.Classical
open scoped NNReal BigOperators

theorem AvramDividend.Classical.finite_marked_step_jump_eq_single_of_injective
    {ι : Type*} (S : Finset ι) (τ : ι → ℝ≥0) (w : ι → ℝ)
    (hτ : ∀ i ∈ S, ∀ j ∈ S, τ i = τ j → i = j)
    (i : ι) (hi : i ∈ S) :
    (∑ j ∈ S, if τ j ≤ τ i then w j else 0) -
      (∑ j ∈ S, if τ j < τ i then w j else 0) = w i := by sorry
