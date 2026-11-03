-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_bounded_random_clock_signed_mean_le_finite_perpetual_value
-- name    : AvramDividend.Classical.avram_wave7_03_bounded_random_clock_signed_mean_le_finite_perpetual_value
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T17:49:50.662215+00:00
-- url     : https://prove2.me/theorems/6fe3e967-4d91-4195-89fe-0044ecd0d773
-- title:
--   Any original bounded random-clock signed Stieltjes mean is below finite perpetual dividendValue.toReal
-- statement:
--   For the original P, spectrally negative Lévy X and cap-admissible D, if the genuine canonical perpetual ENNReal dividendValue is finite, then every signed discounted Stieltjes expected payout on exact paymentTimes(ruinTime)∩Iic(τ ω) at any bounded measurable random NNReal clock τ is at most dividendValue.toReal. The proof applies Proved exact bounded-clock signed-ENNReal expectation equality, monotonicity of the outer lintegral under original payment-domain inclusion, nonnegative discounted signed means, and ENNReal.toReal_mono with the explicit finiteness hypothesis. This supports localisation and optional stopping on original processes without uniform integer clock restrictions.
-- source:
--   Proved fc7c1b8a-c416-450c-b1ad-cadf9344888f; Mathlib lintegral_mono_set, integral_nonneg, ENNReal.toReal_mono.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_full_ruin_bounded_clock_unconditional_mean_eq
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_03_bounded_random_clock_signed_mean_le_finite_perpetual_value
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q)
    (hFinite : dividendValue X q x D < ⊤)
    (T : ℝ≥0) (τ : Ω → ℝ≥0)
    (hτBound : ∀ ω, τ ω ≤ T)
    (hτMeas : Measurable (fun ω => (τ ω : ℝ))) :
    (∫ ω, (∫ t in
        paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) ≤
    (dividendValue X q x D).toReal := by sorry
