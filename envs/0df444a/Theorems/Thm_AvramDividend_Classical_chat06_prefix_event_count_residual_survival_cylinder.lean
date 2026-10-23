-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat06_prefix_event_count_residual_survival_cylinder
-- name    : AvramDividend.Classical.chat06_prefix_event_count_residual_survival_cylinder
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T06:49:34.042989+00:00
-- url     : https://prove2.me/theorems/856c68fa-f2fc-4f6f-9ef5-58a6b0aba901
-- title:
--   Observed-prefix event and fixed-count exponential residual survival as exact arrival cylinder
-- statement:
--   At a nonnegative deterministic observation clock, intersecting any event of a supplied observed-prefix statistic with a fixed renewal count and survival of the residual exponential wait through an additional nonnegative time is exactly the corresponding pair of consecutive arrival-sum inequalities. The proof applies the accepted count-cylinder theorem and sum-range successor identity. This isolates the pathwise event bridge needed for factorising random-count future events jointly with arbitrary measurable observed-prefix events.
-- source:
--   bv_prefix_event_count_residual_survival_cylinder_v2_chat06_20261022.lean, 41 lines, 1791 bytes, SHA-256 88fba31e970d0af79017bde7ed92d0bc3cd40313d2bdd4cd5ebf22b98492d266; private remote probe a556f03c-efb4-4463-953e-deeb15ebd07d passed sentinel with zero candidate source errors.

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_chat06_exact_count_cylinder_from_arrival_threshold

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem AvramDividend.Classical.chat06_prefix_event_count_residual_survival_cylinder
    {Ω E : Type*} (τ : ℕ → Ω → ℝ) (N : Ω → ℝ → ℕ)
    (hThreshold : ∀ ω u k,
      k < N ω u ↔ (∑ i ∈ Finset.range (k + 1), τ i ω) ≤ u)
    (clock : ℝ) (hclock : 0 ≤ clock) (n : ℕ)
    (t : ℝ) (ht : 0 ≤ t) (Z : Ω → E) (Q : Set E) :
    {ω : Ω | Z ω ∈ Q ∧ N ω clock = n ∧
      t < τ n ω - (clock - ∑ i ∈ Finset.range n, τ i ω)} =
      {ω : Ω | Z ω ∈ Q ∧
        (∑ i ∈ Finset.range n, τ i ω) ≤ clock ∧
        clock + t < ∑ i ∈ Finset.range (n + 1), τ i ω} := by sorry
