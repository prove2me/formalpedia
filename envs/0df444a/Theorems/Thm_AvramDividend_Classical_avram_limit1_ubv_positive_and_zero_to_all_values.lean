-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit1_ubv_positive_and_zero_to_all_values
-- name    : AvramDividend.Classical.avram_limit1_ubv_positive_and_zero_to_all_values
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T18:06:29.703109+00:00
-- url     : https://prove2.me/theorems/a002be18-12ac-4594-8ae5-86e95eec98b6
-- title:
--   Original UBV zero-reserve verification completes positive-reserve sources at all capped and unrestricted capital
-- statement:
--   For the genuine original UBV Levy model, assume the source verification candidate is continuous, nonnegative at zero, C2-smooth in the positive cap interior and has slope at least one. Given an upper bound on the actual discounted dividendValue for every strictly positive initial reserve x and every genuine capped admissible dividend strategy D, derive the valueFunctionLe upper bound for every nonnegative capital and, when C=top, the unrestricted valueFunction upper bound. The independently Proved LIMIT-1 zero-capital dividendValue theorem handles x=0 using actual time-zero Stieltjes right-payment, without any positive-x stochastic residual. The Proved local_verification_from_uniform_strategy_bound lifts all actual individual D bounds into the two value functions. No equality-in-law, terminal vanishing or unproved P3/P4 imports.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_limit1_ubv_zero_actual_dividendValue_le
import Theorems.Thm_AvramDividend_Classical_local_verification_from_uniform_strategy_bound

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit1_ubv_positive_and_zero_to_all_values
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (hPositive : ∀ x : ℝ, 0 < x → ENNReal.ofReal x ≤ C →
      ∀ D : ℝ≥0 → Ω → ℝ, IsAdmissibleLe X x C D →
        dividendValue X q x D ≤ ENNReal.ofReal (w x)) :
    (∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      valueFunctionLe X q C x ≤ ENNReal.ofReal (w x)) ∧
    (C = ⊤ → ∀ x : ℝ, 0 ≤ x →
      valueFunction X q x ≤ ENNReal.ofReal (w x)) := by sorry
