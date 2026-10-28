-- Prove2me | Theorems.Thm_AvramDividend_Classical_finite_clock_uniform_cap_expectation_le
-- name    : AvramDividend.Classical.finite_clock_uniform_cap_expectation_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T23:49:48.167273+00:00
-- url     : https://prove2.me/theorems/d069de72-35f3-476d-a5b3-7ac4d72136a7
-- title:
--   Uniform finite-cap bounds control the uncapped finite-record expectation
-- statement:
--   For a measurable potentially infinite record clock, if every integer-horizon-truncated nonnegative payoff expectation is bounded by a constant, then the expected payoff on all finite-record trajectories obeys that bound. This is the final monotone-limit inference needed after proving uniform finite-horizon strong Markov inequalities.
-- source:
--   The Proved finite_clock_reward_lintegral_eq_sup_caps, iSup_le.

import Theorems.Thm_AvramDividend_Classical_finite_clock_reward_lintegral_eq_sup_caps

open MeasureTheory
open AvramDividend.Classical
open scoped ENNReal

theorem AvramDividend.Classical.finite_clock_uniform_cap_expectation_le
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (clock : Ω → ℝ≥0∞) (reward : Ω → ℝ≥0∞)
    (hclock : Measurable clock) (hreward : Measurable reward)
    (bound : ℝ≥0∞)
    (hcap : ∀ n : ℕ,
      (∫⁻ ω, if clock ω ≤ (n : ℝ≥0∞) then reward ω else 0 ∂P) ≤ bound) :
    (∫⁻ ω, if clock ω < ⊤ then reward ω else 0 ∂P) ≤ bound := by sorry
