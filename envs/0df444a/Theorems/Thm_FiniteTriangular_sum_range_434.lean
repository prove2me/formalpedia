-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_434
-- name    : FiniteTriangular.sum_range_434
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:57:27.232672+00:00
-- url     : https://prove2.me/theorems/83749577-c694-4f75-b675-3d7591ab5fd2
-- title:
--   Sum of integers below 434
-- statement:
--   The sum of the nonnegative integers strictly less than $434$ equals $93961$. Equivalently, $\\sum_{k=0}^{434-1} k = 434(434-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_434 : ∑ k ∈ range 434, k = 93961 := by sorry

end FiniteTriangular
