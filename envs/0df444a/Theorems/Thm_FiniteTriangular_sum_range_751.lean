-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_751
-- name    : FiniteTriangular.sum_range_751
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:16:21.249401+00:00
-- url     : https://prove2.me/theorems/b87f13d9-bb33-470a-9786-ea1a5f8bba91
-- title:
--   Sum of integers below 751
-- statement:
--   The sum of the nonnegative integers strictly less than $751$ equals $281625$. Equivalently, $\\sum_{k=0}^{751-1} k = 751(751-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_751 : ∑ k ∈ range 751, k = 281625 := by sorry

end FiniteTriangular
