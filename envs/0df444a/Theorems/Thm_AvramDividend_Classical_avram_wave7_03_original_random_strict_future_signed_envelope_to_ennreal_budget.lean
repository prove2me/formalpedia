-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_random_strict_future_signed_envelope_to_ennreal_budget
-- name    : AvramDividend.Classical.avram_wave7_03_original_random_strict_future_signed_envelope_to_ennreal_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:03:57.432191+00:00
-- url     : https://prove2.me/theorems/c0e22305-87ff-4498-8075-77a836e8b600
-- title:
--   Original signed strict-future random-clock Stieltjes envelope controls the exact ENNReal expected dividend remainder
-- statement:
--   On the original Lévy sample space Ω with its law P and dividendMeasure D ω, fix any original random lower clock T ω. If the genuine discounted real Stieltjes integrand is IntegrableOn paymentTimes(ruinTime X x D ω) ∩ Ioi(T ω) almost surely, its signed integral is bounded by an integrable real random variable B, and E[B]≤K, then the actual double ENNReal future payout over precisely the same original strict-future Stieltjes measure is at most ENNReal.ofReal K. The theorem handles all continuous and right-jump dividends strictly after T; the right-limit payment at the clock itself lies outside the strict tail. It makes no substitution of sample space or process.
-- source:
--   Pinned Mathlib ofReal_integral_eq_lintegral_ofReal with the exact restricted original dividendMeasure, positivity of the exponential, and outer lintegral_mono_ae followed by real integrable domination. Direct adaptation of accepted original perpetual signed envelope theorem 8abf50f8.

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

theorem AvramDividend.Classical.avram_wave7_03_original_random_strict_future_signed_envelope_to_ennreal_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (q : ℝ) (T : Ω → ℝ)
    (B : Ω → ℝ) (K : ℝ)
    (hIntCash : ∀ᵐ ω ∂P,
      IntegrableOn (fun t : ℝ => Real.exp (-(q * t)))
        (paymentTimes (ruinTime X x D ω) ∩ Ioi (T ω)) (dividendMeasure D ω))
    (hSignedBound : ∀ᵐ ω ∂P,
      (∫ t in paymentTimes (ruinTime X x D ω) ∩ Ioi (T ω),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ≤ B ω)
    (hBInt : Integrable B P)
    (hBMean : (∫ ω, B ω ∂P) ≤ K) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Ioi (T ω),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) ≤ ENNReal.ofReal K := by sorry
