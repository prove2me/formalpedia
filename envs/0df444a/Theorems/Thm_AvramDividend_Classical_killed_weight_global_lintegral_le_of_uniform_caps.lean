-- Prove2me | Theorems.Thm_AvramDividend_Classical_killed_weight_global_lintegral_le_of_uniform_caps
-- name    : AvramDividend.Classical.killed_weight_global_lintegral_le_of_uniform_caps
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T00:26:48.749664+00:00
-- url     : https://prove2.me/theorems/62139dd5-5de4-40e5-80a5-016d0bbf4d57
-- title:
--   Uniform capped expectation bound implies global killed reward bound
-- statement:
--   If the killed reward vanishes when its passage clock is infinite, a uniform expected-reward upper bound for every finite natural-horizon cap passes to the global reward by monotone convergence. Establishes the finite-to-infinite step for the stopped renewal inequality.
-- source:
--   Proved cap monotonicity, measurability, supremum recovery, and localised monotone convergence

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_ennreal_killed_weight_eq_iSup_finite_clock_cap
import Theorems.Thm_AvramDividend_Classical_killed_weight_nat_caps_monotone
import Theorems.Thm_AvramDividend_Classical_killed_weight_nat_caps_measurable
import Theorems.Thm_AvramDividend_Classical_monotone_localised_reward_lintegral_le

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.killed_weight_global_lintegral_le_of_uniform_caps
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (T : Ω → ℝ≥0∞) (hT : Measurable T)
    (weight : Ω → ℝ≥0∞) (hw : Measurable weight)
    (hzero : ∀ ω, T ω = ⊤ → weight ω = 0)
    (bound : ℝ≥0∞)
    (hbound : ∀ n : ℕ,
      (∫⁻ ω, if T ω ≤ (n : ℝ≥0∞) then weight ω else 0 ∂P) ≤ bound) :
    (∫⁻ ω, weight ω ∂P) ≤ bound := by sorry
