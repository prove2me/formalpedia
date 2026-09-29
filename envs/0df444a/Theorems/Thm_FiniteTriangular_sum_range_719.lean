-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_719
-- name    : FiniteTriangular.sum_range_719
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:08:39.042732+00:00
-- url     : https://prove2.me/theorems/95701a59-9c54-40c6-a0d3-feda681cfc71
-- title:
--   Sum of integers below 719
-- statement:
--   The sum of the nonnegative integers strictly less than $719$ equals $258121$. Equivalently, $\\sum_{k=0}^{719-1} k = 719(719-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_719 : ∑ k ∈ range 719, k = 258121 := by sorry

end FiniteTriangular
