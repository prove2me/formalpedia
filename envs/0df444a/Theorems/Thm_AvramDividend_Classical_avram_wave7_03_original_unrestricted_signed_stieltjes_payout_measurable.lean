-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_unrestricted_signed_stieltjes_payout_measurable
-- name    : AvramDividend.Classical.avram_wave7_03_original_unrestricted_signed_stieltjes_payout_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:47:15.487527+00:00
-- url     : https://prove2.me/theorems/f78459e8-7ef0-4d60-b5aa-f91c28625614
-- title:
--   Unrestricted actual original real signed Stieltjes dividend payout is measurable on the original probability space
-- statement:
--   Prove genuine global measurability, not merely a.e. measurability under integrability assumptions, of the full actual real discounted Stieltjes dividend payout on the exact original Ω, P, original ruinTime and paymentTimes, actual dividendMeasure. The accepted unrestricted pathwise cash-toReal identity even handles nonintegrable paths with Lean's totalised integral convention. Combine that with Proved global measurability of original ENNReal inner Stieltjes cash and measurable_toReal.
-- source:
--   Proved db59cbee full original ENNReal inner cash measurable; proposed global original same-measure pathwise equality and pinned ENNReal.measurable_toReal.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_perpetual_stieltjes_cash_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_unrestricted_original_signed_stieltjes_eq_cash_toReal_pointwise
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_03_original_unrestricted_signed_stieltjes_payout_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) (q : ℝ) :
    Measurable (fun ω : Ω =>
      ∫ t in paymentTimes (ruinTime X x D ω),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) := by sorry
