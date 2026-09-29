-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1
-- name    : FiniteTriangular.sum_range_1
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:00:14.850341+00:00
-- url     : https://prove2.me/theorems/d6448891-a84d-45a4-bac4-f7e9dbc65a5f
-- title:
--   Sum of integers below 1
-- statement:
--   The sum of the nonnegative integers strictly less than $1$ equals $0$. Equivalently, $\sum_{k=0}^{1-1} k = 1(1-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_1 : ∑ k ∈ range 1, k = 0 := by sorry

end FiniteTriangular
