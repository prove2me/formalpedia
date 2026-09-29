-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_37
-- name    : FiniteTriangular.sum_range_37
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:14:57.911988+00:00
-- url     : https://prove2.me/theorems/abcb30ab-464a-4b4a-a357-7ae68979c498
-- title:
--   Sum of integers below 37
-- statement:
--   The sum of the nonnegative integers strictly less than $37$ equals $666$. Equivalently, $\sum_{k=0}^{37-1} k = 37(37-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_37 : ∑ k ∈ range 37, k = 666 := by sorry

end FiniteTriangular
