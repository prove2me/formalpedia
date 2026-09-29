-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_199
-- name    : FiniteTriangular.sum_range_199
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T07:47:26.664243+00:00
-- url     : https://prove2.me/theorems/b34210e9-0b4f-45f9-bdc8-55dd575e38b5
-- title:
--   Sum of integers below 199
-- statement:
--   The sum of the nonnegative integers strictly less than $199$ equals $19701$. Equivalently, $\\sum_{k=0}^{199-1} k = 199(199-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_199 : ∑ k ∈ range 199, k = 19701 := by sorry

end FiniteTriangular
