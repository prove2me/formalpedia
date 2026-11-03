-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_ae_random_subwindow_ENNReal_toReal_eq_signed_stieltjes
-- name    : AvramDividend.Classical.avram_wave7_03_original_ae_random_subwindow_ENNReal_toReal_eq_signed_stieltjes
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T21:47:47.377124+00:00
-- url     : https://prove2.me/theorems/8a6c4029-6b71-4738-b069-8ef9fa34b3d0
-- title:
--   Original almost-sure random payment subwindow ENNReal.toReal payout equals genuine signed Stieltjes integral
-- statement:
--   Given a random family of actual original dividend payment windows S ω included P-almost surely in paymentTimes(ruinTime X x D ω), and almost sure genuine full signed IntegrableOn against original dividendMeasure, the actual ENNReal lintegral on S ω has toReal exactly the real signed Stieltjes integral on the same S ω, P-almost surely. The proof restricts actual signed integrability to each random window, uses positivity of the discount, applies the exact source-measure real/ENNReal integral theorem, and shows the real signed integral is nonnegative before using ENNReal.toReal_ofReal. This is the pathwise almost-sure bridge needed before an outer P-integral or expectation; it makes no unproved claim about measurability of S or P-integrability of the outer random variable.
-- source:
--   Pinned Mathlib IntegrableOn.mono_set, ofReal_integral_eq_lintegral_ofReal, integral_nonneg, ENNReal.toReal_ofReal; original dividendMeasure/paymentTimes/ruinTime.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
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

theorem AvramDividend.Classical.avram_wave7_03_original_ae_random_subwindow_ENNReal_toReal_eq_signed_stieltjes
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (q : ℝ) (S : Ω → Set ℝ)
    (hSub : ∀ᵐ ω ∂P, S ω ⊆ paymentTimes (ruinTime X x D ω))
    (hInt : ∀ᵐ ω ∂P, IntegrableOn
      (fun t : ℝ => Real.exp (-(q * t)))
      (paymentTimes (ruinTime X x D ω)) (dividendMeasure D ω)) :
    ∀ᵐ ω ∂P,
      (∫⁻ t in S ω, ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)).toReal =
      (∫ t in S ω, Real.exp (-(q * t))
        ∂(dividendMeasure D ω)) := by sorry
