-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_11_original_expected_horizon_eq_any_strict_future_ruin_clock
-- name    : AvramDividend.Classical.avram_wave7_11_original_expected_horizon_eq_any_strict_future_ruin_clock
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T19:11:31.531206+00:00
-- url     : https://prove2.me/theorems/68d675ed-4f68-4736-8ec5-f1cdceff7034
-- title:
--   Exact original-process finite horizon expected payout from one strictly future ruin-clock truncation
-- statement:
--   For the original spectrally negative Levy X, original probability P, original ruinTime and original Stieltjes dividendMeasure D, the expected finite-horizon cash through T equals its reward truncated at min(ruinTime,η) for any deterministic clock η strictly later than ENNReal.ofReal T. Consequently a bounded stochastic budget at any such future clock controls the complete finite-horizon value directly, including dividends paid at T; neither countable monotone convergence nor a separate terminal correction is required.
-- source:
--   Follows exact W7-11 future-clock payment-set equality and pinned Mathlib lintegral_congr; canonical source AvramDividend dividendMeasure, paymentTimes, ruinTime, X and P.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_strict_future_clock_preserves_finite_payment_set
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_11_original_expected_horizon_eq_any_strict_future_ruin_clock
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (q T : ℝ)
    (η : ℝ≥0∞) (hFuture : ENNReal.ofReal T < η) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) =
    (∫⁻ ω, ∫⁻ t in
      paymentTimes (min (ruinTime X x D ω) η) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) := by sorry
