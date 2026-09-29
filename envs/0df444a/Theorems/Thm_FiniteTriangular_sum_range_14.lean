-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_14
-- name    : FiniteTriangular.sum_range_14
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:04:01.23899+00:00
-- url     : https://prove2.me/theorems/26dff558-a4f1-4c0a-8eb2-db3bc87510b1
-- title:
--   Sum of integers below 14
-- statement:
--   The sum of the nonnegative integers strictly less than $14$ equals $91$. Equivalently, $\sum_{k=0}^{14-1} k = 14(14-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_14 : ∑ k ∈ range 14, k = 91 := by sorry

end FiniteTriangular
