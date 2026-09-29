-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_145
-- name    : FiniteTriangular.sum_range_145
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:58:11.330429+00:00
-- url     : https://prove2.me/theorems/e439ca48-d2aa-404e-86c9-af73167eed09
-- title:
--   Sum of integers below 145
-- statement:
--   The sum of the nonnegative integers strictly less than $145$ equals $10440$. Equivalently, $\sum_{k=0}^{145-1} k = 145(145-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_145 : ∑ k ∈ range 145, k = 10440 := by sorry

end FiniteTriangular
