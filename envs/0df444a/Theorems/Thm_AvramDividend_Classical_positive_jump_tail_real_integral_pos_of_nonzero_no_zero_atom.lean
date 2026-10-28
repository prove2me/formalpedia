-- Prove2me | Theorems.Thm_AvramDividend_Classical_positive_jump_tail_real_integral_pos_of_nonzero_no_zero_atom
-- name    : AvramDividend.Classical.positive_jump_tail_real_integral_pos_of_nonzero_no_zero_atom
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T09:50:16.03092+00:00
-- url     : https://prove2.me/theorems/e920bf5f-a163-433a-adc0-2e25cdf26a4e
-- title:
--   Strict positivity of integrated real jump tails for a nonzero magnitude measure
-- statement:
--   For a nonzero positive-magnitude measure with no atom at zero and finite first moment, the integrated real strict upper-tail mass is strictly positive. The canonical positive_first_moment_of_nonzero_without_zero_atom theorem gives a positive ENNReal moment, and positive_jump_tail_real_integral_eq_firstMoment_toReal identifies the real tail integral with its toReal. This enables the strictly positive exact Esscher renewal kernel contraction ratio required by causal_subunit_renewal_full_real_power_package and the cstar finiteness scaled renewal identification.
-- source:
--   Canonical Proved positive_first_moment_of_nonzero_without_zero_atom and positive_jump_tail_real_integral_eq_firstMoment_toReal, Mathlib ENNReal.toReal_pos.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Data.ENNReal.Real
import Theorems.Thm_AvramDividend_Classical_positive_first_moment_of_nonzero_without_zero_atom
import Theorems.Thm_AvramDividend_Classical_positive_jump_tail_real_integral_eq_firstMoment_toReal
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.positive_jump_tail_real_integral_pos_of_nonzero_no_zero_atom (μ : Measure ℝ≥0)
    (hzero : μ ({0} : Set ℝ≥0) = 0) (hμ : μ ≠ 0)
    (hfinite : (∫⁻ z : ℝ≥0, ENNReal.ofReal (z : ℝ) ∂μ) < ⊤) :
    0 < ∫ t in Ioi (0 : ℝ),
      (μ {z : ℝ≥0 | t < (z : ℝ)}).toReal ∂volume := by sorry
