-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_389
-- name    : FiniteTriangular.sum_range_389
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:47:00.858244+00:00
-- url     : https://prove2.me/theorems/6834cb5c-4361-4990-993e-cc11d7fd4926
-- title:
--   Sum of integers below 389
-- statement:
--   The sum of the nonnegative integers strictly less than $389$ equals $75466$. Equivalently, $\\sum_{k=0}^{389-1} k = 389(389-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_389 : ∑ k ∈ range 389, k = 75466 := by sorry

end FiniteTriangular
