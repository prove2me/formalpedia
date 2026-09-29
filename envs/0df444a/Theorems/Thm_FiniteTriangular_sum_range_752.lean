-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_752
-- name    : FiniteTriangular.sum_range_752
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:16:21.176173+00:00
-- url     : https://prove2.me/theorems/faf2ae71-f998-4c68-af44-01be6a47d3ab
-- title:
--   Sum of integers below 752
-- statement:
--   The sum of the nonnegative integers strictly less than $752$ equals $282376$. Equivalently, $\\sum_{k=0}^{752-1} k = 752(752-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_752 : ∑ k ∈ range 752, k = 282376 := by sorry

end FiniteTriangular
