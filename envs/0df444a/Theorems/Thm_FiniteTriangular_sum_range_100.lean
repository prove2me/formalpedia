-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_100
-- name    : FiniteTriangular.sum_range_100
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:45:25.941301+00:00
-- url     : https://prove2.me/theorems/554125fe-be2d-45a8-96c4-73d2e9db248c
-- title:
--   Sum of integers below 100
-- statement:
--   The sum of the nonnegative integers strictly less than $100$ equals $4950$. Equivalently, $\sum_{k=0}^{100-1} k = 100(100-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_100 : ∑ k ∈ range 100, k = 4950 := by sorry

end FiniteTriangular
