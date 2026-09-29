-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_469
-- name    : FiniteTriangular.sum_range_469
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:13:41.35824+00:00
-- url     : https://prove2.me/theorems/5aeeda48-ea71-472c-8962-77909b01e860
-- title:
--   Sum of integers below 469
-- statement:
--   The sum of the nonnegative integers strictly less than $469$ equals $109746$. Equivalently, $\\sum_{k=0}^{469-1} k = 469(469-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_469 : ∑ k ∈ range 469, k = 109746 := by sorry

end FiniteTriangular
