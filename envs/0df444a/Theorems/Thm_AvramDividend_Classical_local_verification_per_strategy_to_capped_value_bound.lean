-- Prove2me | Theorems.Thm_AvramDividend_Classical_local_verification_per_strategy_to_capped_value_bound
-- name    : AvramDividend.Classical.local_verification_per_strategy_to_capped_value_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T06:43:05.009984+00:00
-- url     : https://prove2.me/theorems/26cdad24-50a7-4f19-a856-90135afe6b6b
-- title:
--   A uniform per-admissible-strategy dividend value bound implies the capped value-function bound
-- statement:
--   The capped dividend value function is the supremum of dividendValue X q x D over capped admissible strategies D. Therefore a uniform bound dividendValue≤ENNReal.ofReal(w x) for every such D immediately bounds valueFunctionLe by that value. This isolates the stochastic discounted-dividend verification obligation in the local verification theorem from the purely order-theoretic supremum step.
-- source:
--   Formal definition of valueFunctionLe in the Avram classical dividend model, Mathlib iSup_le.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.local_verification_per_strategy_to_capped_value_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (C : ℝ≥0∞) (x : ℝ) (w : ℝ → ℝ)
    (h : ∀ D : ℝ≥0 → Ω → ℝ, IsAdmissibleLe X x C D →
      dividendValue X q x D ≤ ENNReal.ofReal (w x)) :
    valueFunctionLe X q C x ≤ ENNReal.ofReal (w x) := by sorry
