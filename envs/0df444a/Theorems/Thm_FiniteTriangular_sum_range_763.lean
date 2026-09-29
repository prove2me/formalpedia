-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_763
-- name    : FiniteTriangular.sum_range_763
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:19:36.965411+00:00
-- url     : https://prove2.me/theorems/21e72a98-d69a-4b5a-a0f5-7dca745e7388
-- title:
--   Sum of integers below 763
-- statement:
--   The sum of the nonnegative integers strictly less than $763$ equals $290703$. Equivalently, $\\sum_{k=0}^{763-1} k = 763(763-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_763 : ∑ k ∈ range 763, k = 290703 := by sorry

end FiniteTriangular
