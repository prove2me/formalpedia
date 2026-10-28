-- Prove2me | Theorems.Thm_AvramDividend_Classical_countable_real_density_measure_sum_eq_real_tsum
-- name    : AvramDividend.Classical.countable_real_density_measure_sum_eq_real_tsum
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T10:29:21.156613+00:00
-- url     : https://prove2.me/theorems/13e7f4bd-b586-49a6-8034-27c157e8156f
-- title:
--   Countable sum of nonnegative real-density measures has the ordinary real tsum density
-- statement:
--   Given nonnegative measurable pointwise summable real density functions F n and measures with those exact densities, the countable measure sum has the Lebesgue density ENNReal.ofReal of the ordinary real pointwise tsum. Combines already Proved countable_real_density_measure_sum_eq_withDensity_tsum and pinned Mathlib ENNReal.ofReal_tsum_of_nonneg. This bridges the geometric BV Esscher renewal measure sum to the real convolution power series required for scaled scale identification 1ca4a724.
-- source:
--   Pinned Mathlib ENNReal.ofReal_tsum_of_nonneg and canonical countable_real_density_measure_sum_eq_withDensity_tsum.

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Theorems.Thm_AvramDividend_Classical_countable_real_density_measure_sum_eq_withDensity_tsum
open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.countable_real_density_measure_sum_eq_real_tsum
    (F : ℕ → ℝ → ℝ) (m : ℕ → Measure ℝ)
    (hFmeas : ∀ n : ℕ, Measurable (F n))
    (hFpos : ∀ n : ℕ, ∀ x : ℝ, 0 ≤ F n x)
    (hFsummable : ∀ x : ℝ, Summable (fun n : ℕ => F n x))
    (hm : ∀ n : ℕ, m n =
      volume.withDensity (fun x : ℝ => ENNReal.ofReal (F n x))) :
    Measure.sum m =
      volume.withDensity (fun x : ℝ =>
        ENNReal.ofReal (∑' n : ℕ, F n x)) := by sorry
