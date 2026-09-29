-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_361
-- name    : FiniteTriangular.sum_range_361
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:41:10.936154+00:00
-- url     : https://prove2.me/theorems/b27713e5-988a-46ea-9d6d-821520b328c0
-- title:
--   Sum of integers below 361
-- statement:
--   The sum of the nonnegative integers strictly less than $361$ equals $64980$. Equivalently, $\\sum_{k=0}^{361-1} k = 361(361-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_361 : ∑ k ∈ range 361, k = 64980 := by sorry

end FiniteTriangular
