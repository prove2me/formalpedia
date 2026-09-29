-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_854
-- name    : FiniteTriangular.sum_range_854
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:38:21.948908+00:00
-- url     : https://prove2.me/theorems/0c0ac174-d2d4-43f9-b18d-f5672a266b9e
-- title:
--   Sum of integers below 854
-- statement:
--   The sum of the nonnegative integers strictly less than $854$ equals $364231$. Equivalently, $\\sum_{k=0}^{854-1} k = 854(854-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_854 : ∑ k ∈ range 854, k = 364231 := by sorry

end FiniteTriangular
