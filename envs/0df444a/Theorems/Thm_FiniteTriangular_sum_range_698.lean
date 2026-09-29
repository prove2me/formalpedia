-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_698
-- name    : FiniteTriangular.sum_range_698
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:05:01.127825+00:00
-- url     : https://prove2.me/theorems/751a4e38-ebef-41d5-97a7-0283e45652e2
-- title:
--   Sum of integers below 698
-- statement:
--   The sum of the nonnegative integers strictly less than $698$ equals $243253$. Equivalently, $\\sum_{k=0}^{698-1} k = 698(698-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_698 : ∑ k ∈ range 698, k = 243253 := by sorry

end FiniteTriangular
