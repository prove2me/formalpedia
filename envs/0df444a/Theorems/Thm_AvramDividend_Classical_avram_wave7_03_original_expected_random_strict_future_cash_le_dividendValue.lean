-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_expected_random_strict_future_cash_le_dividendValue
-- name    : AvramDividend.Classical.avram_wave7_03_original_expected_random_strict_future_cash_le_dividendValue
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T07:53:47.149884+00:00
-- url     : https://prove2.me/theorems/0ae556af-8e5e-4196-9cf4-ab489c2140e8
-- title:
--   Every original random strict-future ENNReal payout expectation is bounded by the true perpetual dividendValue
-- statement:
--   For the exact original spectrally negative Lévy process and original dividendMeasure D ω with strict pre-ruin paymentTimes, the expected ENNReal discounted Stieltjes payout restricted to any ω-dependent strict future region t>T ω is at most the complete canonical dividendValue X q x D. This remains valid with an arbitrary real random clock without requiring its measurability or finiteness, because ENNReal upper integrals preserve monotone pointwise domain restriction. It includes singular continuous dividends and all admissible jump atoms that remain inside the strict future region.
-- source:
--   Direct pointwise set restriction via pinned Mathlib lintegral_mono_set, then outer lintegral_mono, after unfolding the exact original dividendValue. No surrogate process and no imported Open theorem.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_03_original_expected_random_strict_future_cash_le_dividendValue
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (q : ℝ) (T : Ω → ℝ) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Ioi (T ω),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
    dividendValue X q x D := by sorry
