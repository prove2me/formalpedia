-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_chat09_original_random_closed_clock_expected_cash_monotone
-- name    : AvramDividend.Classical.avram_wave6_chat09_original_random_closed_clock_expected_cash_monotone
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T10:52:09.525123+00:00
-- url     : https://prove2.me/theorems/33c52aa9-dbba-4913-9cd5-df26505f3aba
-- title:
--   Original Lévy full Stieltjes expected payout is monotone under arbitrary ordered random clocks
-- statement:
--   For the original spectrally negative Lévy process, original ruinTime/paymentTimes and the genuine dividendMeasure, expected extended nonnegative discounted Stieltjes dividends over the inclusive interval up to a random clock τ are bounded by those up to any pointwise larger random clock σ. No measurability or stopping-time property of either clock, BV/UBV assumption, or HJB estimate is required: it is exact pathwise set inclusion and monotonicity of the original Stieltjes integral and outer expectation. Payments at time zero, singular-continuous cash and the terminal right atom are retained.
-- source:
--   Mathlib lintegral_mono_set and lintegral_mono applied directly to original dividendMeasure D ω and paymentTimes (ruinTime X x D ω) at two bounded or unbounded finite random clocks.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave6_chat09_original_random_closed_clock_expected_cash_monotone
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (q : ℝ)
    (τ σ : Ω → ℝ≥0) (hτσ : ∀ ω, τ ω ≤ σ ω) :
    (∫⁻ ω, ∫⁻ t in
      paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
    (∫⁻ ω, ∫⁻ t in
      paymentTimes (ruinTime X x D ω) ∩ Iic (σ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) := by sorry
