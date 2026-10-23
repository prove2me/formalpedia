-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat06_selected_count_increment_exact_positive_cylinder
-- name    : AvramDividend.Classical.chat06_selected_count_increment_exact_positive_cylinder
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T06:30:46.787989+00:00
-- url     : https://prove2.me/theorems/981f5b47-3083-4034-8256-264713917350
-- title:
--   Exact positive renewal-count increment cylinders from consecutive selected arrival thresholds
-- statement:
--   For any sample-path renewal process satisfying the arrival threshold law, exactly m+1 claims occur over a time interval if and only if the selected residual wait together with the next m waits totals at most the interval and adding the following wait exceeds it. This pathwise identity requires no independence and turns selected threshold events into exact increment cylinders.
-- source:
--   bv_selected_count_increment_exact_positive_cylinder_chat06_20261021.lean, 59 lines, 2258 bytes, SHA-256 64440097106986b5ed754f96c0e3d9f1a2e0d730f3d8632a9cfaf850d73d953b; private remote probe 0472bb49-d775-436d-97b5-12ce7e36e30b reached sentinel with no candidate source errors.

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Data.Real.Basic
import Theorems.Thm_AvramDividend_Classical_chat06_selected_future_count_increment_event

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem AvramDividend.Classical.chat06_selected_count_increment_exact_positive_cylinder
    {Ω : Type*} (τ : Ω → ℕ → ℝ) (N : Ω → ℝ → ℕ)
    (hThreshold : ∀ ω u k,
      k < N ω u ↔ (∑ i ∈ Finset.range (k + 1), τ ω i) ≤ u)
    (clock t : ℝ) (m : ℕ) :
    {ω : Ω | N ω (clock + t) - N ω clock = m + 1} =
      {ω : Ω |
        ((∑ i ∈ Finset.range (N ω clock + 1), τ ω i) - clock) +
          (∑ j ∈ Finset.range m, τ ω (N ω clock + 1 + j)) ≤ t ∧
        t < ((∑ i ∈ Finset.range (N ω clock + 1), τ ω i) - clock) +
          (∑ j ∈ Finset.range (m + 1), τ ω (N ω clock + 1 + j))} := by sorry
