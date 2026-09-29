-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_462
-- name    : FiniteTriangular.sum_range_462
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:11:46.545643+00:00
-- url     : https://prove2.me/theorems/6a50f21a-7754-4f77-8fff-d93121de4b76
-- title:
--   Sum of integers below 462
-- statement:
--   The sum of the nonnegative integers strictly less than $462$ equals $106491$. Equivalently, $\\sum_{k=0}^{462-1} k = 462(462-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_462 : ∑ k ∈ range 462, k = 106491 := by sorry

end FiniteTriangular
