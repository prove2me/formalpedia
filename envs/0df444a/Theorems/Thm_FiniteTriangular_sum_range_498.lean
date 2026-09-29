-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_498
-- name    : FiniteTriangular.sum_range_498
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:20:23.313381+00:00
-- url     : https://prove2.me/theorems/61e0f0a2-d5d3-444f-9dd1-673971d2c772
-- title:
--   Sum of integers below 498
-- statement:
--   The sum of the nonnegative integers strictly less than $498$ equals $123753$. Equivalently, $\\sum_{k=0}^{498-1} k = 498(498-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_498 : ∑ k ∈ range 498, k = 123753 := by sorry

end FiniteTriangular
