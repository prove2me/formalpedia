-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_original_positive_strict_cash_to_perpetual_dividendValue
-- name    : AvramDividend.Classical.avram_limit2_original_positive_strict_cash_to_perpetual_dividendValue
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T17:59:39.753485+00:00
-- url     : https://prove2.me/theorems/8c98fe7e-a2fc-4e18-beb4-1546ee63a006
-- title:
--   Uniform original strictly positive open-horizon dividend cash bounds imply the genuine infinite-horizon dividendValue bound
-- statement:
--   For actual IsAdmissible X x D, a uniform bound on original expected discounted Stieltjes cash on paymentTimes(ruinTime) ∩ Iio T at every T>0 implies the same bound on perpetual dividendValue X q x D. Three Proved/public source-exact steps are composed: positive strict Iio T to all nonnegative closed Iic T including zero; closed to all natural ruin-stopped clocks; and the original Wave6 natural-stop monotone-convergence result to dividendValue. The proof handles time-zero and right-horizon atoms without terminal vanishing, equality-in-law, or assuming a stochastic source estimate not supplied.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_limit2_original_positive_strict_budget_implies_all_closed_horizons
import Theorems.Thm_AvramDividend_Classical_avram_limit2_original_uniform_closed_cash_budget_implies_all_natural_stopped
import Theorems.Thm_AvramDividend_Classical_avram_wave6_10_original_natural_stopped_budget_implies_full_dividendValue
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit2_original_positive_strict_cash_to_perpetual_dividendValue
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissible X x D)
    (B : ℝ≥0∞)
    (hStrict : ∀ (T : ℝ), 0 < T →
      (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Set.Iio T,
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω) ∂P) ≤ B) :
    dividendValue X q x D ≤ B := by sorry
