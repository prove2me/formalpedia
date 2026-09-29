-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_25
-- name    : FiniteTriangular.sum_range_25
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:08:27.148392+00:00
-- url     : https://prove2.me/theorems/4af09bbc-f721-4fa8-8fd9-1c28417f3d03
-- title:
--   Sum of integers below 25
-- statement:
--   The sum of the nonnegative integers strictly less than $25$ equals $300$. Equivalently, $\sum_{k=0}^{25-1} k = 25(25-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_25 : ∑ k ∈ range 25, k = 300 := by sorry

end FiniteTriangular
