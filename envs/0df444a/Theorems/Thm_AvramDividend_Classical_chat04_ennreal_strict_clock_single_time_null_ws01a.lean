-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_ennreal_strict_clock_single_time_null_ws01a
-- name    : AvramDividend.Classical.chat04_ennreal_strict_clock_single_time_null_ws01a
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T18:06:18.567501+00:00
-- url     : https://prove2.me/theorems/ce7cc42c-0501-4571-8536-174f82830247
-- title:
--   Every fixed extended nonnegative clock is hit at a Lebesgue-null set of real times
-- statement:
--   For any extended nonnegative real clock τ, including τ=+∞, the set of nonnegative real times t whose ENNReal coercion equals τ has Lebesgue measure zero. This allows the strict-lower-clock killed resolvent and the closed-history killed semigroup to be identified almost everywhere in their time integrals, without a scale harmonicity hypothesis.
-- source:
--   Definition of ENNReal.toReal, the theorem ENNReal.toReal_ofReal, Lebesgue-null singleton and monotonicity of null sets, in Mathlib.

import Mathlib.Probability.Distributions.Exponential
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass

open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.chat04_ennreal_strict_clock_single_time_null_ws01a (τ : ℝ≥0∞) :
    (volume : Measure ℝ) {t : ℝ | 0 ≤ t ∧ ENNReal.ofReal t = τ} = 0 := by sorry
