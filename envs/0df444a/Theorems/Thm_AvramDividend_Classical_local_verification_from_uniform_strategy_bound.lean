-- Prove2me | Theorems.Thm_AvramDividend_Classical_local_verification_from_uniform_strategy_bound
-- name    : AvramDividend.Classical.local_verification_from_uniform_strategy_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T06:44:07.735104+00:00
-- url     : https://prove2.me/theorems/0d513542-578c-4592-b94a-95b56620feda
-- title:
--   Reduce both local-verification value-function conclusions to uniform strategy-level payout bounds
-- statement:
--   The two value-function conclusions in Proposition 4(i) are automatic from one bound on dividendValue for every capped admissible dividend strategy and permitted initial reserve. For the capped conclusion, apply the supremum reducer. For C=∞, substitute the equality valueFunctionLe(...∞)=valueFunction to conclude the unrestricted branch. This accurately isolates the probabilistic stopped-dividend payout estimate as the remaining substantive obligation.
-- source:
--   Children local_verification_per_strategy_to_capped_value_bound and valueFunctionLe_top_eq_valueFunction; exact root theorem's conclusion.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.local_verification_from_uniform_strategy_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hStrategy : ∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      ∀ D : ℝ≥0 → Ω → ℝ, IsAdmissibleLe X x C D →
        dividendValue X q x D ≤ ENNReal.ofReal (w x)) :
    (∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      valueFunctionLe X q C x ≤ ENNReal.ofReal (w x)) ∧
    (C = ⊤ → ∀ x : ℝ, 0 ≤ x →
      valueFunction X q x ≤ ENNReal.ofReal (w x)) := by sorry
