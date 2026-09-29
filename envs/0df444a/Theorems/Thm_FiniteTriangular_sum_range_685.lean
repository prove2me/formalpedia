-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_685
-- name    : FiniteTriangular.sum_range_685
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:01:48.027881+00:00
-- url     : https://prove2.me/theorems/61e1d397-926d-48a8-930c-0d253d7a1a9b
-- title:
--   Sum of integers below 685
-- statement:
--   The sum of the nonnegative integers strictly less than $685$ equals $234270$. Equivalently, $\\sum_{k=0}^{685-1} k = 685(685-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_685 : ∑ k ∈ range 685, k = 234270 := by sorry

end FiniteTriangular
