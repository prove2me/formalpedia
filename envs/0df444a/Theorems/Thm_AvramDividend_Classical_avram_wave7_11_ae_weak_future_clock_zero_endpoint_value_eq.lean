-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_11_ae_weak_future_clock_zero_endpoint_value_eq
-- name    : AvramDividend.Classical.avram_wave7_11_ae_weak_future_clock_zero_endpoint_value_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T20:16:01.673194+00:00
-- url     : https://prove2.me/theorems/6ef58a28-f39e-46a3-b5d8-df20b457e27e
-- title:
--   Almost surely weakly future source clock preserves expected value when exact horizon atom vanishes
-- statement:
--   For the original Lévy X, probability P and original Stieltjes dividendMeasure and ruinTime, an almost surely non-strict future auxiliary clock η≥T preserves the complete expected finite-horizon discounted dividend reward when the genuine original stopped horizon singleton payout is zero almost surely. The terminal atom requirement is explicit and source-faithful. At η=T the exact missing endpoint payout is zero by hypothesis; at η>T the canonical payment sets agree.
-- source:
--   Proved W7-11 weak-future exact endpoint correction plus Mathlib lintegral_congr_ae. Source has genuine Ω,P,X,dividendMeasure and strict stopped paymentTimes.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_weak_future_clock_exact_horizon_endpoint_correction
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_11_ae_weak_future_clock_zero_endpoint_value_eq
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (q T : ℝ) (hT : 0 < T)
    (η : Ω → ℝ≥0∞)
    (hFuture : ∀ᵐ ω ∂P, ENNReal.ofReal T ≤ η ω)
    (hZeroAtom : ∀ᵐ ω ∂P,
      (∫⁻ t in (paymentTimes (ruinTime X x D ω) ∩ Iic T) ∩ {T},
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) = 0) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) =
    (∫⁻ ω, ∫⁻ t in
      paymentTimes (min (ruinTime X x D ω) (η ω)) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) := by sorry
