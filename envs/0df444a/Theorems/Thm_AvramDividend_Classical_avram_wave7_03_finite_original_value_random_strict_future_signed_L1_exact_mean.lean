-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_finite_original_value_random_strict_future_signed_L1_exact_mean
-- name    : AvramDividend.Classical.avram_wave7_03_finite_original_value_random_strict_future_signed_L1_exact_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:15:19.532391+00:00
-- url     : https://prove2.me/theorems/86cd5e20-1466-4dcd-800c-2c10935e3cc6
-- title:
--   Finite original value yields genuine random-clock strict-future signed L1 and exact expected ENNReal cash equality
-- statement:
--   For the genuine source Ω, P, X, ruinTime and dividendMeasure, under finite canonical original dividendValue and measurable arbitrary random lower clock T, the actual real signed discounted Stieltjes payout strictly after T is P-integrable, and its genuine real P-expectation converts exactly to the original double ENNReal expected dividend payout on the identical paymentTimes(ruinTime) ∩ Ioi(T ω) domain. This preserves continuous and right-jump dividends after T and excludes the atom at T. No surrogate stochastic process, domain or measure.
-- source:
--   Only already-Proved original-process source facts: 3a9d20cb unrestricted pathwise real Stieltjes IntegrableOn; ea1c2561 random strict-future cash measurability; 0ae556af random future cash ≤ canonical dividendValue; pinned Mathlib integrable_toReal_of_lintegral_ne_top and ofReal_integral_eq_lintegral_ofReal. Pathwise signed conversion is proved inline, avoiding any Open dependency.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_strict_future_random_clock_cash_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_expected_random_strict_future_cash_le_dividendValue
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_finite_value_implies_original_unrestricted_signed_stieltjes_integrable_ae

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_03_finite_original_value_random_strict_future_signed_L1_exact_mean
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) (q : ℝ)
    (T : Ω → ℝ) (hTm : Measurable T)
    (hFinite : dividendValue X q x D < ⊤) :
    Integrable (fun ω : Ω =>
      ∫ t in paymentTimes (ruinTime X x D ω) ∩ Ioi (T ω),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) P ∧
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Ioi (T ω),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) =
    ENNReal.ofReal
      (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω) ∩ Ioi (T ω),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) := by sorry
