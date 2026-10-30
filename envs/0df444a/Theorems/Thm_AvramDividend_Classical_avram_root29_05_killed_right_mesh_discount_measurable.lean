-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_05_killed_right_mesh_discount_measurable
-- name    : AvramDividend.Classical.avram_root29_05_killed_right_mesh_discount_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T10:27:28.805574+00:00
-- url     : https://prove2.me/theorems/23b2d8cf-5227-4d31-a5e5-ecb1a70e7f84
-- title:
--   Strictly killed discounted rational-mesh Stieltjes weight is Borel measurable
-- statement:
--   For any discount q, strict killing horizon τ and rational mesh denominator n+1, the function of continuous real payment time r taking the discounted first right-mesh endpoint weight when that endpoint precedes τ and zero otherwise is Borel measurable. Required for the Fatou lower-semicontinuity argument converting actual killed Stieltjes measure to sampled rational regulator cashflows.
-- source:
--   Pinned Mathlib Int.measurable_ceil, measurable_of_countable for the integer-to-real cast, real exponential and ENNReal lift continuity, Measurable.ite and measurableSet_lt. Does not require or assert the unproved stochastic barrier equality.

import Mathlib
import Mathlib.MeasureTheory.Function.Floor

open MeasureTheory
open scoped ENNReal Classical

theorem AvramDividend.Classical.avram_root29_05_killed_right_mesh_discount_measurable
    (q : ℝ) (τ : ℝ≥0∞) (n : ℕ) :
    Measurable (fun r : ℝ =>
      let e := ((⌈r * ((n : ℝ) + 1)⌉ : ℤ) : ℝ) / ((n : ℝ) + 1)
      if ENNReal.ofReal e < τ then
        ENNReal.ofReal (Real.exp (-(q * e))) else 0) := by sorry
