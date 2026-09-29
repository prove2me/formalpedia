-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_368
-- name    : FiniteTriangular.sum_range_368
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:41:14.332236+00:00
-- url     : https://prove2.me/theorems/9f74265b-15be-43a0-bfaf-71bb04eaa453
-- title:
--   Sum of integers below 368
-- statement:
--   The sum of the nonnegative integers strictly less than $368$ equals $67528$. Equivalently, $\\sum_{k=0}^{368-1} k = 368(368-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_368 : ∑ k ∈ range 368, k = 67528 := by sorry

end FiniteTriangular
