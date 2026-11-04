-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_finite_continuous_test_sum_tendsto
-- name    : AvramDividend.Classical.avram_p2_a_zero_rate_finite_continuous_test_sum_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T17:11:28.6222+00:00
-- url     : https://prove2.me/theorems/05e8a22e-6ed6-46c5-8363-770860ec94bb
-- title:
--   Finite sums of compact continuous tests inherit original mesh pointwise limits
-- statement:
--   For a fixed finite set of genuine jump times, each selected grid increment tends to its true jump mark. Prove that any continuous real test applied to these increments converges after finite summation, by finite-set induction and continuity of addition. This is the finite-matching part of the original negative compact-test grid-to-jump proof; it uses no rate or compensator assumption.

import Mathlib

open Filter Topology

theorem AvramDividend.Classical.avram_p2_a_zero_rate_finite_continuous_test_sum_tendsto
    {α : Type*} (s : Finset α)
    (a : α → ℕ → ℝ) (b : α → ℝ)
    (f : ℝ → ℝ) (hf : Continuous f)
    (h : ∀ u ∈ s, Tendsto (a u) atTop (𝓝 (b u))) :
    Tendsto (fun n : ℕ => ∑ u ∈ s, f (a u n))
      atTop (𝓝 (∑ u ∈ s, f (b u))) := by sorry
