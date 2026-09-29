-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_738
-- name    : FiniteTriangular.sum_range_738
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:14:29.63354+00:00
-- url     : https://prove2.me/theorems/46af51c9-04b1-431c-8c3a-95a325a416aa
-- title:
--   Sum of integers below 738
-- statement:
--   The sum of the nonnegative integers strictly less than $738$ equals $271953$. Equivalently, $\\sum_{k=0}^{738-1} k = 738(738-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_738 : ∑ k ∈ range 738, k = 271953 := by sorry

end FiniteTriangular
