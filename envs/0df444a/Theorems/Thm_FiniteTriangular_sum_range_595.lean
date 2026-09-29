-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_595
-- name    : FiniteTriangular.sum_range_595
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:42:59.477234+00:00
-- url     : https://prove2.me/theorems/bc445235-bb75-46a4-a127-71048ba826ed
-- title:
--   Sum of integers below 595
-- statement:
--   The sum of the nonnegative integers strictly less than $595$ equals $176715$. Equivalently, $\\sum_{k=0}^{595-1} k = 595(595-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_595 : ∑ k ∈ range 595, k = 176715 := by sorry

end FiniteTriangular
