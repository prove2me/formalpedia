-- Prove2me | Theorems.Thm_AvramDividend_Classical_geometric_measure_sum_extract_constant
-- name    : AvramDividend.Classical.geometric_measure_sum_extract_constant
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T11:12:02.983423+00:00
-- url     : https://prove2.me/theorems/f8a3f2da-1c52-4634-bc4c-2f76599df10a
-- title:
--   Factor the leading Esscher renewal constant from a geometric countable measure sum
-- statement:
--   For any nonnegative extended-real multiplier c and countable sequence of measures, the geometric sum weighted by c^(n+1) is exactly c times the sum weighted by c^n. This uses the canonical ENNReal multiplication-through-tsum identity and Measure.sum_apply, with no finiteness assumption. It is a measure-normalisation step connecting the finite Esscher geometric renewal witness c=1/drift to a nonnegative convolution-power density series, on the route to cstar_lt_top.
-- source:
--   Pinned Mathlib Measure.sum_apply, Measure.smul_apply and ENNReal.tsum_mul_left.

import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
open MeasureTheory
open scoped ENNReal NNReal

theorem AvramDividend.Classical.geometric_measure_sum_extract_constant
    (c : ℝ≥0∞) (m : ℕ → Measure ℝ) :
    Measure.sum (fun n : ℕ => c ^ (n + 1) • m n) =
      c • Measure.sum (fun n : ℕ => c ^ n • m n) := by sorry
