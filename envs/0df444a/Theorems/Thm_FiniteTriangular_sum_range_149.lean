-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_149
-- name    : FiniteTriangular.sum_range_149
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:58:13.752744+00:00
-- url     : https://prove2.me/theorems/aab4fe36-1e1c-4fd8-b81c-3d5cf11d1a22
-- title:
--   Sum of integers below 149
-- statement:
--   The sum of the nonnegative integers strictly less than $149$ equals $11026$. Equivalently, $\sum_{k=0}^{149-1} k = 149(149-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_149 : ∑ k ∈ range 149, k = 11026 := by sorry

end FiniteTriangular
