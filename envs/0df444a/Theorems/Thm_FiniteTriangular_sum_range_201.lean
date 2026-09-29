-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_201
-- name    : FiniteTriangular.sum_range_201
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T07:49:14.703958+00:00
-- url     : https://prove2.me/theorems/9f49ea09-a201-46e7-a842-d49bc083cf17
-- title:
--   Sum of integers below 201
-- statement:
--   The sum of the nonnegative integers strictly less than $201$ equals $20100$. Equivalently, $\\sum_{k=0}^{201-1} k = 201(201-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_201 : ∑ k ∈ range 201, k = 20100 := by sorry

end FiniteTriangular
