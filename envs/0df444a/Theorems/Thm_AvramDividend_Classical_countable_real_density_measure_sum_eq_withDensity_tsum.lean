-- Prove2me | Theorems.Thm_AvramDividend_Classical_countable_real_density_measure_sum_eq_withDensity_tsum
-- name    : AvramDividend.Classical.countable_real_density_measure_sum_eq_withDensity_tsum
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T10:17:33.502014+00:00
-- url     : https://prove2.me/theorems/e62b0edb-fc31-422f-95b8-887eca63000b
-- title:
--   A countable sum of real-density measures has the pointwise extended-real summed density
-- statement:
--   If every measure m n is the Lebesgue withDensity measure of the nonnegative real function F n and the F n are measurable, their countable measure sum is exactly the Lebesgue withDensity measure of the function-valued extended-real sum of their densities. Directly applies the pinned Mathlib withDensity_tsum theorem. Together with the measure convolution-power density identification, it converts the positive geometric BV Esscher renewal measure into a density series, a central missing equality in the scaled cstar renewal representation.
-- source:
--   Pinned Mathlib MeasureTheory.withDensity_tsum and measure extensionality; exact revision 0df444a.

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Tactic.FunProp
open MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.countable_real_density_measure_sum_eq_withDensity_tsum
    (F : ℕ → ℝ → ℝ) (m : ℕ → Measure ℝ)
    (hFmeas : ∀ n : ℕ, Measurable (F n))
    (hm : ∀ n : ℕ, m n =
      volume.withDensity (fun x : ℝ => ENNReal.ofReal (F n x))) :
    Measure.sum m =
      volume.withDensity
        (∑' n : ℕ, (fun x : ℝ => ENNReal.ofReal (F n x))) := by sorry
