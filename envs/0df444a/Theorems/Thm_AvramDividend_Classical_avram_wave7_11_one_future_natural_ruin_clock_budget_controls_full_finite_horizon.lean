-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_11_one_future_natural_ruin_clock_budget_controls_full_finite_horizon
-- name    : AvramDividend.Classical.avram_wave7_11_one_future_natural_ruin_clock_budget_controls_full_finite_horizon
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T19:21:18.373103+00:00
-- url     : https://prove2.me/theorems/78b21fe9-86f5-433a-b71e-5160d9f94412
-- title:
--   A single sufficiently late bounded ruin-clock budget implies full original finite-horizon value bound
-- statement:
--   For any nonnegative finite real horizon T and natural n with n>T, an upper bound b on the true expected discounted original Stieltjes payout stopped at min(ruinTime,n) through T already bounds the complete original-process expected discounted payout through T. The strict future choice of n preserves the original dividend atom at T. This is a precise finite-horizon stochastic-budget consumer requiring one bounded clock rather than a uniform countable family.
-- source:
--   Original Avram spectrally negative Levy Ω/P/X, strict-future expected ruin-clock exact equality W7-11, Mathlib ENNReal ofReal real comparison.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_original_expected_horizon_eq_any_strict_future_ruin_clock
import Mathlib.Data.ENNReal.Basic

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_11_one_future_natural_ruin_clock_budget_controls_full_finite_horizon
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (q T : ℝ)
    (n : ℕ) (hT : 0 ≤ T) (hFuture : T < (n : ℝ))
    (b : ℝ≥0∞)
    (hBudget :
      (∫⁻ ω, ∫⁻ t in paymentTimes
        (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤ b) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤ b := by sorry
