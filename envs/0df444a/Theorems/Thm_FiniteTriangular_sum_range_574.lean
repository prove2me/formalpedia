-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_574
-- name    : FiniteTriangular.sum_range_574
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:37:44.478878+00:00
-- url     : https://prove2.me/theorems/0c7f8039-3a2c-433d-bc94-73c5024d91e3
-- title:
--   Sum of integers below 574
-- statement:
--   The sum of the nonnegative integers strictly less than $574$ equals $164451$. Equivalently, $\\sum_{k=0}^{574-1} k = 574(574-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_574 : ∑ k ∈ range 574, k = 164451 := by sorry

end FiniteTriangular
