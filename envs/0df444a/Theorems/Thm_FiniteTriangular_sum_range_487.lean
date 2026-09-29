-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_487
-- name    : FiniteTriangular.sum_range_487
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:17:12.733579+00:00
-- url     : https://prove2.me/theorems/acdabc33-0759-4150-b457-d5ed99dfe81e
-- title:
--   Sum of integers below 487
-- statement:
--   The sum of the nonnegative integers strictly less than $487$ equals $118341$. Equivalently, $\\sum_{k=0}^{487-1} k = 487(487-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_487 : ∑ k ∈ range 487, k = 118341 := by sorry

end FiniteTriangular
