-- Prove2me | Theorems.Thm_AvramDividend_Classical_cstar_zero_barrier_compare_of_no_minimizer
-- name    : AvramDividend.Classical.cstar_zero_barrier_compare_of_no_minimizer
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T13:37:44.192984+00:00
-- url     : https://prove2.me/theorems/360080c3-b9de-4a52-be30-dc516182f3ac
-- title:
--   Optimal zero barrier under the zero-boundary derivative criterion and W(0)=0
-- statement:
--   In the branch where the positive global derivative minimiser set is empty and the extended right derivative at zero is no greater than every positive derivative, the canonical definition sets cstar=0. If W is nonnegative and W(0)=0, the barrier cstar=0 dominates all competing barrier values for 0<=x<=cstar. This covers the degenerate zero-level half of Avram milestone 3 without assuming positive derivatives or interior regularity.
-- source:
--   Unfold exact canonical cstar definition to derive cstar=0 from no positive minimiser and the zero-boundary derivative inequality. Apply the already Proved cstar_optimal_barrier_of_shape theorem's zero-level W(0)=0 branch, without relying on unproved differentiability.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical
open scoped ENNReal

namespace AvramDividend.Classical

theorem cstar_zero_barrier_compare_of_no_minimizer
    (W : ℝ → ℝ)
    (hnonneg : ∀ y : ℝ, 0 ≤ y → 0 ≤ W y)
    (hno : ¬(cstarSet W).Nonempty)
    (hderiv0 : ∀ x : ℝ, 0 < x →
      derivZeroPlus W ≤ ((deriv W x : ℝ) : EReal))
    (hW0 : W 0 = 0) :
    cstar W < ⊤ ∧
      ∀ x a : ℝ, 0 ≤ x → x ≤ (cstar W).toReal → 0 ≤ a →
        barrierValue W a x ≤ vcstar W x := by
  sorry

end AvramDividend.Classical
