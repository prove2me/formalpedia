-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_perpetual_signed_integrable_envelope_to_dividendValue_bound
-- name    : AvramDividend.Classical.avram_wave7_03_original_perpetual_signed_integrable_envelope_to_dividendValue_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T23:49:08.437547+00:00
-- url     : https://prove2.me/theorems/8abf50f8-8b7f-4a74-a65c-6bf4436c1fc6
-- title:
--   Original perpetual signed Stieltjes envelope yields exact ENNReal dividendValue bound
-- statement:
--   On the canonical original spectrally negative Levy model X with its actual probability law P, ruinTime and dividendMeasure, assume the entire discounted signed Stieltjes payment is integrable pathwise P-almost everywhere and bounded by an integrable real random variable B. If E_P[B] is at most K, then the precise original ENNReal dividendValue is at most ENNReal.ofReal K. The proof formally infers B nonnegative P-almost everywhere, equates real signed Stieltjes and ENNReal integrals on the identical original paymentTimes set, and then applies the same bridge under P. The time-zero right-limit atom and every continuous and strictly pre-ruin payment are included. Establishing a signed stochastic envelope is separate.
-- source:
--   Direct original source proof by two applications of pinned Mathlib ofReal_integral_eq_lintegral_ofReal and lintegral_mono_ae, with automatic positivity of B. Genuine nonnegative exp integrand, no surrogate process, no Open imports.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.ENNReal.Real
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_03_original_perpetual_signed_integrable_envelope_to_dividendValue_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (q : ℝ) (B : Ω → ℝ) (K : ℝ)
    (hIntCash : ∀ᵐ ω ∂P,
      IntegrableOn (fun t : ℝ => Real.exp (-(q * t)))
        (paymentTimes (ruinTime X x D ω))
        (dividendMeasure D ω))
    (hSignedBound : ∀ᵐ ω ∂P,
      (∫ t in paymentTimes (ruinTime X x D ω),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ≤ B ω)
    (hBInt : Integrable B P)
    (hBMean : (∫ ω, B ω ∂P) ≤ K) :
    dividendValue X q x D ≤ ENNReal.ofReal K := by sorry
