-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_808
-- name    : FiniteTriangular.sum_range_808
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:28:11.052277+00:00
-- url     : https://prove2.me/theorems/1be9155e-a49b-46e3-b667-f67f5278bdbe
-- title:
--   Sum of integers below 808
-- statement:
--   The sum of the nonnegative integers strictly less than $808$ equals $326028$. Equivalently, $\\sum_{k=0}^{808-1} k = 808(808-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_808 : ∑ k ∈ range 808, k = 326028 := by sorry

end FiniteTriangular
