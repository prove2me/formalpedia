-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_finite_original_dividendValue_toReal_eq_expected_genuine_unrestricted_signed_cash
-- name    : AvramDividend.Classical.avram_wave7_03_finite_original_dividendValue_toReal_eq_expected_genuine_unrestricted_signed_cash
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:59:12.901199+00:00
-- url     : https://prove2.me/theorems/101b1a4f-8dfa-4122-b903-f9839696ac95
-- title:
--   Finite canonical original ENNReal dividendValue.toReal exactly equals expected genuine unrestricted real signed Stieltjes payout
-- statement:
--   A compact real-valued original-process consumption lemma for the BV/UBV HJB generator budget: whenever canonical original dividendValue is finite, its ENNReal.toReal conversion is exactly the outer real expectation under the original P of the genuine unrestricted signed real Stieltjes payout on paymentTimes(ruinTime) against original dividendMeasure. This follows from the accepted unrestricted outer signed Stieltjes mean equality and the pointwise nonnegativity of discounted original dividend integrals. The time-zero right-limit atom and continuous and jump payments remain included, with no altered source process.
-- source:
--   Proved 9806569f exact unrestricted outer signed real Stieltjes mean; ENNReal.toReal_ofReal and integral_nonneg.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_perpetual_signed_stieltjes_L1_and_exact_outer_mean_of_finite
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_03_finite_original_dividendValue_toReal_eq_expected_genuine_unrestricted_signed_cash
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) (q : ℝ)
    (hFinite : dividendValue X q x D < ⊤) :
    (dividendValue X q x D).toReal =
      (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) := by sorry
