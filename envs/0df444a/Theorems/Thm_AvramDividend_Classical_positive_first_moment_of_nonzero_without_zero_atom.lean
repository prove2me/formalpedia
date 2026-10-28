-- Prove2me | Theorems.Thm_AvramDividend_Classical_positive_first_moment_of_nonzero_without_zero_atom
-- name    : AvramDividend.Classical.positive_first_moment_of_nonzero_without_zero_atom
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T09:25:34.576226+00:00
-- url     : https://prove2.me/theorems/5eb27024-a3fc-449a-97be-ab3c8ab46567
-- title:
--   Positive jump first moment from a nonzero magnitude measure with no zero atom
-- statement:
--   Any nonzero Borel measure on the nonnegative reals with zero mass at the origin has a strictly positive, possibly infinite, extended-real first moment. Because ENNReal.ofReal z is positive exactly off zero, lintegral_pos_iff_support and the null singleton imply the claim. This is the measure-theoretic positivity bridge for the BV Esscher jump-magnitude renewal kernel: standing BV provides a nonzero signed Lévy jump measure, and the Lévy-measure zero atom plus negative-to-magnitude pushforward supplies the hypotheses.
-- source:
--   Pinned Mathlib MeasureTheory.lintegral_pos_iff_support, measure_union_le and measure_univ_eq_zero.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Data.ENNReal.Real
import Mathlib.Tactic.FunProp
open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.positive_first_moment_of_nonzero_without_zero_atom (μ : Measure ℝ≥0)
    (hzero : μ ({0} : Set ℝ≥0) = 0) (hμ : μ ≠ 0) :
    0 < ∫⁻ z : ℝ≥0, ENNReal.ofReal (z : ℝ) ∂μ := by sorry
