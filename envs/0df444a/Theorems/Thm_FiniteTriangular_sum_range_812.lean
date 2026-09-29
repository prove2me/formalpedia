-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_812
-- name    : FiniteTriangular.sum_range_812
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:29:53.470242+00:00
-- url     : https://prove2.me/theorems/c0051c65-0929-4ed7-ab7b-706d0c3e8db1
-- title:
--   Sum of integers below 812
-- statement:
--   The sum of the nonnegative integers strictly less than $812$ equals $329266$. Equivalently, $\\sum_{k=0}^{812-1} k = 812(812-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_812 : ∑ k ∈ range 812, k = 329266 := by sorry

end FiniteTriangular
