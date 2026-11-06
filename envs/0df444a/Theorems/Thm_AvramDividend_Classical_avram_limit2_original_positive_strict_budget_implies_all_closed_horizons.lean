-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_original_positive_strict_budget_implies_all_closed_horizons
-- name    : AvramDividend.Classical.avram_limit2_original_positive_strict_budget_implies_all_closed_horizons
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T17:51:43.847051+00:00
-- url     : https://prove2.me/theorems/315b2d12-ffb6-4653-bb6f-9de0a281dee3
-- title:
--   Strict positive original ruin-clock cash bounds give all closed horizon cash bounds including zero
-- statement:
--   For the actual original ruinTime and Stieltjes dividendMeasure, a uniform expected discounted cash bound on paymentTimes(ruinTime) ∩ Iio T for every strictly positive T implies the identical bound on every nonnegative closed Iic T horizon. The closed endpoint at T is retained by moving to the strictly later strict endpoint T+1; the publicly Proved cash monotonicity 4f845e71 gives pathwise inclusion and expected cash comparison. At T=0 the original initial-payment atom is retained, with no zero-clock discontinuity assumption, terminal vanishing, or equality-in-law.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_limit2_strict_later_real_horizon_cash_dominates_closed
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit2_original_positive_strict_budget_implies_all_closed_horizons
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (B : ℝ≥0∞)
    (hStrict : ∀ (T : ℝ), 0 < T →
      (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Set.Iio T,
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω) ∂P) ≤ B) :
    ∀ (T : ℝ), 0 ≤ T →
      (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Set.Iic T,
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω) ∂P) ≤ B := by sorry
