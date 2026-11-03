-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_unrestricted_original_signed_stieltjes_eq_cash_toReal_pointwise
-- name    : AvramDividend.Classical.avram_wave7_03_unrestricted_original_signed_stieltjes_eq_cash_toReal_pointwise
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:37:15.379528+00:00
-- url     : https://prove2.me/theorems/c2ee0732-fece-4959-83da-d0ae9b9815d6
-- title:
--   Global pointwise identity of genuine original unrestricted real Stieltjes integral and ENNReal cash.toReal with explicit nonintegrable convention
-- statement:
--   For every original Levy path, any real discount, and original admissible dividend strategy, the totalised real full unrestricted Stieltjes payout against exactly the source dividendMeasure on paymentTimes(ruinTime) is the real conversion of the ENNReal inner cash. On genuinely integrable paths this is the positive integral identity. On paths of infinite ENNReal payout, the real integral uses the Mathlib integral_undef convention and equals zero, just as ENNReal.toReal top=0; this explicitly does not claim integrability on infinite-cash paths. Original time-zero atom and continuous and jump payouts are unchanged.
-- source:
--   Pinned Mathlib lintegral_ofReal_ne_top_iff_integrable, ofReal_integral_eq_lintegral_ofReal, integral_undef and exact original source Definitions.

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

theorem AvramDividend.Classical.avram_wave7_03_unrestricted_original_signed_stieltjes_eq_cash_toReal_pointwise
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) (ω : Ω) (q : ℝ) :
    (∫⁻ t in paymentTimes (ruinTime X x D ω),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)).toReal =
      (∫ t in paymentTimes (ruinTime X x D ω),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) := by sorry
