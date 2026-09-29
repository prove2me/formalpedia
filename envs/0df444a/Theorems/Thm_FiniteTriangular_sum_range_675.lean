-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_675
-- name    : FiniteTriangular.sum_range_675
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:59:59.066656+00:00
-- url     : https://prove2.me/theorems/58fe53da-0632-4759-9c4a-103d8d9645d9
-- title:
--   Sum of integers below 675
-- statement:
--   The sum of the nonnegative integers strictly less than $675$ equals $227475$. Equivalently, $\\sum_{k=0}^{675-1} k = 675(675-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_675 : ∑ k ∈ range 675, k = 227475 := by sorry

end FiniteTriangular
