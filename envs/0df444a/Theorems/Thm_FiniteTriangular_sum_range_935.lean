-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_935
-- name    : FiniteTriangular.sum_range_935
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:55:11.366499+00:00
-- url     : https://prove2.me/theorems/63a39971-4b36-4242-9b36-1e421dffac7c
-- title:
--   Sum of integers below 935
-- statement:
--   The sum of the nonnegative integers strictly less than $935$ equals $436645$. Equivalently, $\\sum_{k=0}^{935-1} k = 935(935-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_935 : ∑ k ∈ range 935, k = 436645 := by sorry

end FiniteTriangular
