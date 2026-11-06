-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_sweep16_original_strategywise_cap_budget_to_both_values
-- name    : AvramDividend.Classical.avram_sweep16_original_strategywise_cap_budget_to_both_values
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T18:49:14.539193+00:00
-- url     : https://prove2.me/theorems/3ebf5fbb-d0be-4efd-9c91-fe635eb490b9
-- title:
--   Original admissible-strategy dividend budgets imply capped and unrestricted variational upper bounds
-- statement:
--   A source-exact bridge at the true original-process value-function boundary. Every pointwise discounted dividendValue upper bound for each capped admissible strategy yields the capped valueFunctionLe upper via its literal double iSup definition. At cap C=top, the already-Proved exact top-cap/unrestricted identity yields the unrestricted value upper. The theorem does not assume generator inequalities, stochastic martingale identities or any Open canonical verification parent. It is a reusable noncircular adapter allowing two positive-reserve strategy budgets to feed local_verification directly.

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_valueFunctionLe_top_eq_valueFunction

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_sweep16_original_strategywise_cap_budget_to_both_values
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hStrategy : ∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      ∀ D : ℝ≥0 → Ω → ℝ, IsAdmissibleLe X x C D →
        dividendValue X q x D ≤ ENNReal.ofReal (w x)) :
    (∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      valueFunctionLe X q C x ≤ ENNReal.ofReal (w x)) ∧
    (C = ⊤ → ∀ x : ℝ, 0 ≤ x →
      valueFunction X q x ≤ ENNReal.ofReal (w x)) := by sorry
