-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_65
-- name    : FiniteTriangular.sum_range_65
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:32:50.885877+00:00
-- url     : https://prove2.me/theorems/b6670f43-54d7-4688-bbc5-632ea3e4eb1f
-- title:
--   Sum of integers below 65
-- statement:
--   The sum of the nonnegative integers strictly less than $65$ equals $2080$. Equivalently, $\sum_{k=0}^{65-1} k = 65(65-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_65 : ∑ k ∈ range 65, k = 2080 := by sorry

end FiniteTriangular
