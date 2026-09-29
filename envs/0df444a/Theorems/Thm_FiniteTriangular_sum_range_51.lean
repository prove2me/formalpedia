-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_51
-- name    : FiniteTriangular.sum_range_51
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:18:58.042848+00:00
-- url     : https://prove2.me/theorems/45c32cbc-cc85-40b6-b7d5-45c794fc1416
-- title:
--   Sum of integers below 51
-- statement:
--   The sum of the nonnegative integers strictly less than $51$ equals $1275$. Equivalently, $\sum_{k=0}^{51-1} k = 51(51-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_51 : ∑ k ∈ range 51, k = 1275 := by sorry

end FiniteTriangular
