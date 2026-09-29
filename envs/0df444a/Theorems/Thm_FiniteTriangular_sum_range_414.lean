-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_414
-- name    : FiniteTriangular.sum_range_414
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:52:06.541652+00:00
-- url     : https://prove2.me/theorems/14d4243d-9c3a-4091-84df-c96d4be5ab1b
-- title:
--   Sum of integers below 414
-- statement:
--   The sum of the nonnegative integers strictly less than $414$ equals $85491$. Equivalently, $\\sum_{k=0}^{414-1} k = 414(414-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_414 : ∑ k ∈ range 414, k = 85491 := by sorry

end FiniteTriangular
