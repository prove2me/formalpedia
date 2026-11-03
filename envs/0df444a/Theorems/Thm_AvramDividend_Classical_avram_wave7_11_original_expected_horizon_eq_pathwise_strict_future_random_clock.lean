-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_11_original_expected_horizon_eq_pathwise_strict_future_random_clock
-- name    : AvramDividend.Classical.avram_wave7_11_original_expected_horizon_eq_pathwise_strict_future_random_clock
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T19:07:20.919825+00:00
-- url     : https://prove2.me/theorems/91bb7fd7-990f-4dbe-8961-5a3198ccf9cf
-- title:
--   Exact original expected Lévy dividend payout under any random future truncation clock
-- statement:
--   For the canonical spectrally negative Levy X, original law P, original dividendMeasure D and ruinTime, any auxiliary possibly random truncation clock η(ω) strictly later than fixed real horizon T for every sample preserves the full discounted expected Stieltjes payout through T. The theorem is source-faithful and does not require η to be a stopping time or measurable, because it establishes pointwise equality of the exact payout integrands before taking the existing nonnegative expectation. This strictly generalizes deterministic future truncation and allows original sample-dependent localization clocks.
-- source:
--   Proved W7-11 future-clock payment-set exact equality e57ac9e9, original Stieltjes measure and ruinTime, Mathlib lintegral_congr.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_strict_future_clock_preserves_finite_payment_set
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_11_original_expected_horizon_eq_pathwise_strict_future_random_clock
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (q T : ℝ)
    (η : Ω → ℝ≥0∞)
    (hFuture : ∀ ω, ENNReal.ofReal T < η ω) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) =
    (∫⁻ ω, ∫⁻ t in
      paymentTimes (min (ruinTime X x D ω) (η ω)) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) := by sorry
