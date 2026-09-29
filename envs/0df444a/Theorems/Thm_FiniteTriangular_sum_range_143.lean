-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_143
-- name    : FiniteTriangular.sum_range_143
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:57:02.57107+00:00
-- url     : https://prove2.me/theorems/81dfdd61-6d6b-4aaa-aed8-ab3722ef546d
-- title:
--   Sum of integers below 143
-- statement:
--   The sum of the nonnegative integers strictly less than $143$ equals $10153$. Equivalently, $\sum_{k=0}^{143-1} k = 143(143-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_143 : ∑ k ∈ range 143, k = 10153 := by sorry

end FiniteTriangular
