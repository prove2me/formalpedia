-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_645
-- name    : FiniteTriangular.sum_range_645
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:53:14.545914+00:00
-- url     : https://prove2.me/theorems/d3cf1e55-9fff-4a31-ac78-3cd34dec1dbc
-- title:
--   Sum of integers below 645
-- statement:
--   The sum of the nonnegative integers strictly less than $645$ equals $207690$. Equivalently, $\\sum_{k=0}^{645-1} k = 645(645-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_645 : ∑ k ∈ range 645, k = 207690 := by sorry

end FiniteTriangular
