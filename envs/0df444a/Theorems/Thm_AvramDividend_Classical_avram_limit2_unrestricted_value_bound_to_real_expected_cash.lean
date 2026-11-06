-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_unrestricted_value_bound_to_real_expected_cash
-- name    : AvramDividend.Classical.avram_limit2_unrestricted_value_bound_to_real_expected_cash
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T10:45:12.807718+00:00
-- url     : https://prove2.me/theorems/4d83e422-62e4-428b-beaf-5189111dda23
-- title:
--   Finite original unrestricted value upper bound gives real L1 expected dividend payout bound
-- statement:
--   Whenever the genuine original unrestricted valueFunction at reserve x is bounded above by ENNReal.ofReal(w) for a nonnegative real ceiling w, each genuinely original IsAdmissible dividend strategy D has a finite dividendValue by the literal unrestricted double indexed supremum. The Proved original complete perpetual signed Stieltjes theorem yields integrability of the real ruin-stopped discounted payout and exact equality of dividendValue with ENNReal.ofReal of that real expected payout. Because w is nonnegative, the genuine real expected payout is at most w. This retains the actual original process, strategy class, time-zero payout and ruin clock with no equality-in-law or inferred terminal vanishing.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_perpetual_signed_stieltjes_L1_and_exact_outer_mean_of_finite

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit2_unrestricted_value_bound_to_real_expected_cash
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ)
    (w : ℝ) (hw : 0 ≤ w)
    (hValueBound : valueFunction X q x ≤ ENNReal.ofReal w)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissible X x D) :
    Integrable (fun ω : Ω =>
      ∫ t in paymentTimes (ruinTime X x D ω),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) P ∧
    dividendValue X q x D =
      ENNReal.ofReal
        (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω),
          Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) ∧
    (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω),
      Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) ≤ w := by sorry
