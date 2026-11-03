-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_random_clock_integrable_signed_envelope_to_exact_expected_ENNReal_budget
-- name    : AvramDividend.Classical.avram_wave7_03_original_random_clock_integrable_signed_envelope_to_exact_expected_ENNReal_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T22:10:44.92023+00:00
-- url     : https://prove2.me/theorems/298a1040-a41c-4c84-acfb-1a3446bf186a
-- title:
--   Actual original stopped signed Stieltjes budget plus integrable nonnegative random envelope implies expected ENNReal bound
-- statement:
--   For genuine source spectrally negative Lévy process X, original P and dividendMeasure D ω, let τ be any real random clock. Suppose original pre-ruin discounted signed Stieltjes cash through τ is pathwise IntegrableOn and ≤ a real random terminal envelope B P-a.e. If B is truly P-integrable, P-a.e nonnegative and has real expectation ≤ K, then the expected original double ENNReal discounted Stieltjes cash is ≤ ENNReal.ofReal K on exactly paymentTimes(ruinTime)∩Iic τ. This explicitly certifies the missing integrability and nonnegativity assumptions before crossing the real/ENNReal boundary; includes zero, continuous and horizon right-payment atoms.
-- source:
--   Pinned Mathlib exact ofReal_integral_eq_lintegral_ofReal on both original inner Stieltjes measure and P outer measure, lintegral_mono_ae and ENNReal.ofReal_le_ofReal; no Open imports.

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

theorem AvramDividend.Classical.avram_wave7_03_original_random_clock_integrable_signed_envelope_to_exact_expected_ENNReal_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (q : ℝ) (τ B : Ω → ℝ) (K : ℝ)
    (hIntCash : ∀ᵐ ω ∂P,
      IntegrableOn (fun t : ℝ => Real.exp (-(q * t)))
        (paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω))
        (dividendMeasure D ω))
    (hSignedBound : ∀ᵐ ω ∂P,
      (∫ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ≤ B ω)
    (hBInt : Integrable B P)
    (hBPos : 0 ≤ᵐ[P] B)
    (hBMean : (∫ ω, B ω ∂P) ≤ K) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) ≤ ENNReal.ofReal K := by sorry
