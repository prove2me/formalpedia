-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_481
-- name    : FiniteTriangular.sum_range_481
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:17:11.026276+00:00
-- url     : https://prove2.me/theorems/c823c844-ac23-4c7a-9b01-05c488fd323a
-- title:
--   Sum of integers below 481
-- statement:
--   The sum of the nonnegative integers strictly less than $481$ equals $115440$. Equivalently, $\\sum_{k=0}^{481-1} k = 481(481-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_481 : ∑ k ∈ range 481, k = 115440 := by sorry

end FiniteTriangular
