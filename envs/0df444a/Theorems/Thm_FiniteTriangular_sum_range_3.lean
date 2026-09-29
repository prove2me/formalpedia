-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_3
-- name    : FiniteTriangular.sum_range_3
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:00:28.6641+00:00
-- url     : https://prove2.me/theorems/97e52100-e657-4509-9df5-e1b5de2e8cb8
-- title:
--   Sum of integers below 3
-- statement:
--   The sum of the nonnegative integers strictly less than $3$ equals $3$. Equivalently, $\sum_{k=0}^{3-1} k = 3(3-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_3 : ∑ k ∈ range 3, k = 3 := by sorry

end FiniteTriangular
