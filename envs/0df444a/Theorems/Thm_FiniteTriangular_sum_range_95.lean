-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_95
-- name    : FiniteTriangular.sum_range_95
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:43:41.858662+00:00
-- url     : https://prove2.me/theorems/381e5d23-abdf-4bbd-afc2-b594e5998476
-- title:
--   Sum of integers below 95
-- statement:
--   The sum of the nonnegative integers strictly less than $95$ equals $4465$. Equivalently, $\sum_{k=0}^{95-1} k = 95(95-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_95 : ∑ k ∈ range 95, k = 4465 := by sorry

end FiniteTriangular
