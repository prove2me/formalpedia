-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_135
-- name    : FiniteTriangular.sum_range_135
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:55:53.290329+00:00
-- url     : https://prove2.me/theorems/09d3ff47-4361-4bb2-a5f3-bc1fe9b69f5c
-- title:
--   Sum of integers below 135
-- statement:
--   The sum of the nonnegative integers strictly less than $135$ equals $9045$. Equivalently, $\sum_{k=0}^{135-1} k = 135(135-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_135 : ∑ k ∈ range 135, k = 9045 := by sorry

end FiniteTriangular
