-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_true_strict_closed_exponential_product_integral_ws01a
-- name    : AvramDividend.Classical.chat04_true_strict_closed_exponential_product_integral_ws01a
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T09:23:35.500678+00:00
-- url     : https://prove2.me/theorems/f9d7ced7-c563-4c82-aae5-4e112d2bdc31
-- title:
--   Actual Exp-clock strict lower killing equals closed-history killing for arbitrary nonnegative measurable rewards
-- statement:
--   At a genuine independent exponential time of positive rate, the joint product-law integral of every nonnegative jointly measurable reward killed by strict lower first passage equals that killed by survival of the complete closed path history. It relies on the previously proved almost-everywhere-in-time boundary lemma and positive-clock density, not a false pointwise equivalence.
-- source:
--   Proved 26b1bbb5 a.e.-time clock equivalence, joint strict event measurable c740e195, closed-history joint event measurability, Mathlib Tonelli lintegral_prod and exponential withDensity.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_chat04_strict_lower_killed_closed_history_ae_time_ws01a
import Theorems.Thm_AvramDividend_Classical_chat04_exponential_clock_strict_lower_killing_joint_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_closed_history_lower_survival_joint_measurable_ws01a
open AvramDividend.Classical MeasureTheory ProbabilityTheory Set Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_true_strict_closed_exponential_product_integral_ws01a
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (p : ℝ) (hp : 0 < p) (x : ℝ)
    (R : Ω × ℝ → ℝ≥0∞) (hR : Measurable R) :
    (∫⁻ z : Ω × ℝ,
      ({z : Ω × ℝ | 0 ≤ z.2 ∧
        ENNReal.ofReal z.2 < twoSidedExitDownTime X (-x) z.1}).indicator R z
      ∂(P.prod (ProbabilityTheory.expMeasure p))) =
    (∫⁻ z : Ω × ℝ,
      ({z : Ω × ℝ | 0 ≤ z.2 ∧
        ∀ s : ℝ≥0, s ≤ Real.toNNReal z.2 → -x ≤ X.X s z.1}).indicator R z
      ∂(P.prod (ProbabilityTheory.expMeasure p))) := by sorry
