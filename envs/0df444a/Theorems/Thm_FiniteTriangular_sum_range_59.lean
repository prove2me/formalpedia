-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_59
-- name    : FiniteTriangular.sum_range_59
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:21:14.524985+00:00
-- url     : https://prove2.me/theorems/dca0ccd6-bafd-4efc-adbd-5aa95a713dc6
-- title:
--   Sum of integers below 59
-- statement:
--   The sum of the nonnegative integers strictly less than $59$ equals $1711$. Equivalently, $\sum_{k=0}^{59-1} k = 59(59-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_59 : ∑ k ∈ range 59, k = 1711 := by sorry

end FiniteTriangular
