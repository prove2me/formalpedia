-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_678
-- name    : FiniteTriangular.sum_range_678
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:59:59.916282+00:00
-- url     : https://prove2.me/theorems/6ef6aad8-3758-41d1-ba31-670e4b6c4499
-- title:
--   Sum of integers below 678
-- statement:
--   The sum of the nonnegative integers strictly less than $678$ equals $229503$. Equivalently, $\\sum_{k=0}^{678-1} k = 678(678-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_678 : ∑ k ∈ range 678, k = 229503 := by sorry

end FiniteTriangular
