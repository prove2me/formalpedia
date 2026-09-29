-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_321
-- name    : FiniteTriangular.sum_range_321
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:32:09.640974+00:00
-- url     : https://prove2.me/theorems/76774eee-815e-466b-87e8-a42f2a4b764f
-- title:
--   Sum of integers below 321
-- statement:
--   The sum of the nonnegative integers strictly less than $321$ equals $51360$. Equivalently, $\\sum_{k=0}^{321-1} k = 321(321-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_321 : ∑ k ∈ range 321, k = 51360 := by sorry

end FiniteTriangular
