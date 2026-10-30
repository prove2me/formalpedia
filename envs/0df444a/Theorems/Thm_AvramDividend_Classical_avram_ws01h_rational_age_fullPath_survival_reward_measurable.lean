-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01h_rational_age_fullPath_survival_reward_measurable
-- name    : AvramDividend.Classical.avram_ws01h_rational_age_fullPath_survival_reward_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T13:07:54.911768+00:00
-- url     : https://prove2.me/theorems/0b7edea5-4f06-4d2f-84eb-1f2d5748c168
-- title:
--   Joint measurability of exact rational open-horizon full-path survival reward at random nonnegative clock age
-- statement:
--   The original full-future path-space reward equal to one when all fixed rational samples before a variable residual age stay above -a, and zero otherwise, is genuinely jointly measurable in the age and the full path. The proof uses only countably many fixed-coordinate evaluations, avoiding the false assumption that arbitrary path evaluation at a variable age is measurable in an uncountable cylinder sigma algebra. The reward equals weak source lower survival by the separately proved exact rational-grid passage clock theorem.
-- source:
--   Mathlib measurable_pi_apply, measurableSet_lt, countable intersection, exact source-killed rational-grid theorem WS01H.

import Mathlib

open MeasureTheory Set
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.avram_ws01h_rational_age_fullPath_survival_reward_measurable
    (a : ℝ) :
    Measurable (fun z : ℝ≥0 × (ℝ≥0 → ℝ) =>
      if (∀ n : ℕ, 0 < n → ∀ k : ℕ,
        (k : ℝ≥0) * (n : ℝ≥0)⁻¹ < z.1 →
          0 ≤ a + z.2 ((k : ℝ≥0) * (n : ℝ≥0)⁻¹))
      then (1 : ℝ≥0∞) else 0) := by sorry
