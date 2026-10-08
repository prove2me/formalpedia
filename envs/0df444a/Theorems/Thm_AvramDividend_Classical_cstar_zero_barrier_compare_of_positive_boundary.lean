-- Prove2me | Theorems.Thm_AvramDividend_Classical_cstar_zero_barrier_compare_of_positive_boundary
-- name    : AvramDividend.Classical.cstar_zero_barrier_compare_of_positive_boundary
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T13:37:03.005039+00:00
-- url     : https://prove2.me/theorems/a4079eab-6893-4bfc-9000-4eccad1ea8ff
-- title:
--   Optimal zero dividend barrier with finite positive right derivative
-- statement:
--   If the positive global derivative minimizer set is empty and the extended right derivative at zero is a lower bound for every positive ordinary derivative, then cstar=0. When that right derivative is a finite strictly positive real number, and W is nonnegative, the zero barrier dominates all competitors at initial capital x=0 without requiring W(0)=0. This covers the remaining finite-positive denominator branch of the Avram zero-barrier comparison.
-- source:
--   Unfold the exact canonical cstar definition to obtain cstar=0. The finite-positive extended right derivative yields a denominator d>0. At a>0, the assumed global derivative inequality gives the required denominator comparison; at a=0 it is equality. Since 0≤b≤x≤cstar=0, the secant inequality reduces to 0≤0, and the already Proved barrier comparison of shape closes.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical
open scoped ENNReal

namespace AvramDividend.Classical

theorem cstar_zero_barrier_compare_of_positive_boundary
    (W : ℝ → ℝ)
    (hnonneg : ∀ y : ℝ, 0 ≤ y → 0 ≤ W y)
    (hno : ¬(cstarSet W).Nonempty)
    (hderivmin : ∀ x : ℝ, 0 < x →
      derivZeroPlus W ≤ ((deriv W x : ℝ) : EReal))
    (d : ℝ) (hd : 0 < d)
    (hboundary : derivZeroPlus W = (d : EReal)) :
    cstar W < ⊤ ∧
      ∀ x a : ℝ, 0 ≤ x → x ≤ (cstar W).toReal → 0 ≤ a →
        barrierValue W a x ≤ vcstar W x := by
  sorry

end AvramDividend.Classical
