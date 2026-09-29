-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_110
-- name    : FiniteTriangular.sum_range_110
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:47:12.364317+00:00
-- url     : https://prove2.me/theorems/5c88638e-1ef4-4048-bfb0-bdf5f014b99e
-- title:
--   Sum of integers below 110
-- statement:
--   The sum of the nonnegative integers strictly less than $110$ equals $5995$. Equivalently, $\sum_{k=0}^{110-1} k = 110(110-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_110 : ∑ k ∈ range 110, k = 5995 := by sorry

end FiniteTriangular
