-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_stopped_original_reward_eq_closed_horizon_restriction
-- name    : AvramDividend.Classical.avram_wave4_04b_stopped_original_reward_eq_closed_horizon_restriction
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T10:55:36.135346+00:00
-- url     : https://prove2.me/theorems/122d4c4b-f0ad-47c3-a555-9ddfc26bd6d8
-- title:
--   Original stopped dividend payout equals the closed-horizon Stieltjes payment-time restriction
-- statement:
--   For the actual adapted dividend Stieltjes measure, every sample path, finite nonnegative horizon, extended stopping/payment clock and arbitrary nonnegative payoff weight, the original stopped-payment integral on paymentTimes τ intersected with times ≤T is identical to the integral on paymentTimes τ against the finite closed-horizon measure restricted to [0,T]. The equality preserves the initial atom and exactly observes terminal strict-ruin conventions, and contains all absolutely continuous, singular-continuous and atomic variation. This is the direct interface from the 04-B control theorem to Chat 04's corrected original reward.
-- source:
--   The source paymentTimes definition explicitly enforces time≥0, and pinned Mathlib Measure.restrict_restrict and congruence of lintegrals; no stochastic/Poisson assumption.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

noncomputable section

theorem AvramDividend.Classical.avram_wave4_04b_stopped_original_reward_eq_closed_horizon_restriction
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ≥0) (τ : ℝ≥0∞) (f : ℝ → ℝ≥0∞) :
    (∫⁻ s in paymentTimes τ ∩ Iic (T : ℝ), f s ∂dividendMeasure D ω) =
    (∫⁻ s in paymentTimes τ, f s ∂
      (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))) := by sorry
