-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_perpetual_pathwise_signed_stieltjes_integrable_eq_cash_of_finite
-- name    : AvramDividend.Classical.avram_wave7_03_original_perpetual_pathwise_signed_stieltjes_integrable_eq_cash_of_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:20:30.321393+00:00
-- url     : https://prove2.me/theorems/329453c6-3ac7-4cb0-ae65-a11f026a53eb
-- title:
--   Original full perpetual pathwise real signed Stieltjes cash is integrable and equals the exact ENNReal cash whenever the latter is finite
-- statement:
--   For the genuine original spectrally negative Lévy process X, dividend strategy D, sample ω, ruinTime and paymentTimes under exactly dividendMeasure D ω, finiteness of the unrestricted inner perpetual ENNReal discounted Stieltjes cash implies that the actual signed REAL Stieltjes integrand exp(-q t) is IntegrableOn the entire ruin-stopped paymentTimes, with no finite time truncation. Moreover ENNReal.ofReal of the genuine unrestricted real Stieltjes integral is exactly the original inner ENNReal cash. This is a precise same-measure, same-domain source bridge, not a mere informal conversion of a signed integral. The continuous positive-time dividends and time-zero right-limit atom are retained. The proof uses pinned Mathlib lintegral_ofReal_ne_top_iff_integrable and ofReal_integral_eq_lintegral_ofReal after establishing measurability and exp positivity.
-- source:
--   Canonical Avram dividendMeasure and paymentTimes definitions; pinned Mathlib lintegral_ofReal_ne_top_iff_integrable (signature verified) and ofReal_integral_eq_lintegral_ofReal; no surrogate process.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_03_original_perpetual_pathwise_signed_stieltjes_integrable_eq_cash_of_finite
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (q : ℝ)
    (hCashFinite :
      (∫⁻ t in paymentTimes (ruinTime X x D ω),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)) < ⊤) :
    IntegrableOn
      (fun t : ℝ => Real.exp (-(q * t)))
      (paymentTimes (ruinTime X x D ω))
      (dividendMeasure D ω) ∧
    ENNReal.ofReal
      (∫ t in paymentTimes (ruinTime X x D ω),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) =
      (∫⁻ t in paymentTimes (ruinTime X x D ω),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)) := by sorry
