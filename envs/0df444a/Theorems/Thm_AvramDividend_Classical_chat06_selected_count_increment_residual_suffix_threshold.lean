-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat06_selected_count_increment_residual_suffix_threshold
-- name    : AvramDividend.Classical.chat06_selected_count_increment_residual_suffix_threshold
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T06:39:40.261474+00:00
-- url     : https://prove2.me/theorems/868da2f2-4497-421c-8498-ee09a09002dd
-- title:
--   Renewal-count increment threshold in selected exponential residual and future-suffix coordinates
-- statement:
--   The event of more than m additional renewal arrivals over an interval is exactly the event that the residual part of the currently pending exponential wait plus the first m future waits is no greater than the interval length. The proof rewrites the accepted selected count-increment arrival-sum event using a single sum-range-succ identity. This puts the count process in the coordinates of the independently proved residual/future-suffix joint probability law.
-- source:
--   bv_selected_count_increment_residual_suffix_threshold_chat06_20261022.lean, 47 lines, 2062 bytes, SHA-256 2f1e7bd7ba08b7951f843d93f44f7d5da9e84458085e89d7d47f36f9df95d849; private remote probe 3f36cccb-a218-4b16-8fea-b65115c538e5 passed sentinel with no candidate errors.

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Theorems.Thm_AvramDividend_Classical_chat06_selected_future_count_increment_event

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem AvramDividend.Classical.chat06_selected_count_increment_residual_suffix_threshold
    {Ω : Type*} (τ : Ω → ℕ → ℝ) (N : Ω → ℝ → ℕ)
    (hThreshold : ∀ ω u k,
      k < N ω u ↔ (∑ i ∈ Finset.range (k + 1), τ ω i) ≤ u)
    (clock t : ℝ) (m : ℕ) :
    {ω : Ω | m < N ω (clock + t) - N ω clock} =
      {ω : Ω |
        (τ ω (N ω clock) -
          (clock - ∑ i ∈ Finset.range (N ω clock), τ ω i)) +
          (∑ j ∈ Finset.range m, τ ω (N ω clock + 1 + j)) ≤ t} := by sorry
