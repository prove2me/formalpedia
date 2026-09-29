-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_244
-- name    : FiniteTriangular.sum_range_244
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T07:59:14.408203+00:00
-- url     : https://prove2.me/theorems/4a5f3895-a62e-4565-8c7a-3c3f76b5264d
-- title:
--   Sum of integers below 244
-- statement:
--   The sum of the nonnegative integers strictly less than $244$ equals $29646$. Equivalently, $\\sum_{k=0}^{244-1} k = 244(244-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_244 : ∑ k ∈ range 244, k = 29646 := by sorry

end FiniteTriangular
