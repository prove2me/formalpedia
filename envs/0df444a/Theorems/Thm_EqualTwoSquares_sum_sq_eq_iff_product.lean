-- Prove2me | Theorems.Thm_EqualTwoSquares_sum_sq_eq_iff_product
-- name    : EqualTwoSquares.sum_sq_eq_iff_product
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-09-26T11:25:44.806987+00:00
-- url     : https://prove2.me/theorems/6ea6b5a3-fbed-4ca9-a429-adc11290be66
-- title:
--   The sum-of-squares equation rewritten as a product equation
-- statement:
--   For integers a, b, c and d, the equality a^2 + b^2 = c^2 + d^2 holds if and only if (a + c)(a - c) = (d + b)(d - b).
-- source:
--   Mission target; no machine-checked proof yet.

import Mathlib

namespace EqualTwoSquares

/-- Objective 4, rearrangement: the sum-of-squares equation rewritten as a product equation. -/
theorem sum_sq_eq_iff_product (a b c d : ℤ) :
    a^2 + b^2 = c^2 + d^2 ↔ (a + c) * (a - c) = (d + b) * (d - b) := by sorry

end EqualTwoSquares
