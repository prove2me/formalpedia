-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_9
-- name    : FiniteTriangular.sum_range_9
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:00:47.478203+00:00
-- url     : https://prove2.me/theorems/69f73ad6-da12-4804-90a5-6981a6be9c48
-- title:
--   Sum of integers below 9
-- statement:
--   The sum of the nonnegative integers strictly less than $9$ equals $36$. Equivalently, $\sum_{k=0}^{9-1} k = 9(9-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_9 : ∑ k ∈ range 9, k = 36 := by sorry

end FiniteTriangular
