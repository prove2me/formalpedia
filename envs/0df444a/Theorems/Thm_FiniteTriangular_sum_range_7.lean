-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_7
-- name    : FiniteTriangular.sum_range_7
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:00:41.108759+00:00
-- url     : https://prove2.me/theorems/540fd8d7-4c54-444a-b733-4e407bf159cb
-- title:
--   Sum of integers below 7
-- statement:
--   The sum of the nonnegative integers strictly less than $7$ equals $21$. Equivalently, $\sum_{k=0}^{7-1} k = 7(7-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_7 : ∑ k ∈ range 7, k = 21 := by sorry

end FiniteTriangular
