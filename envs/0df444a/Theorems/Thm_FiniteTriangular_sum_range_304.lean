-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_304
-- name    : FiniteTriangular.sum_range_304
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T08:19:54.430164+00:00
-- url     : https://prove2.me/theorems/f5f59899-25ef-41da-93d4-c1cec41596b0
-- title:
--   Sum of integers below 304
-- statement:
--   The sum of the nonnegative integers strictly less than $304$ equals $46056$. Equivalently, $\\sum_{k=0}^{304-1} k = 304(304-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_304 : ∑ k ∈ range 304, k = 46056 := by sorry

end FiniteTriangular
