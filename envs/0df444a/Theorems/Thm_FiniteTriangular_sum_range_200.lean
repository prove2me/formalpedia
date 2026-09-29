-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_200
-- name    : FiniteTriangular.sum_range_200
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T07:47:20.522195+00:00
-- url     : https://prove2.me/theorems/4e0ee1be-4ca3-4c5f-8e87-915826a246d7
-- title:
--   Sum of integers below 200
-- statement:
--   The sum of the nonnegative integers strictly less than $200$ equals $19900$. Equivalently, $\\sum_{k=0}^{200-1} k = 200(200-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_200 : ∑ k ∈ range 200, k = 19900 := by sorry

end FiniteTriangular
