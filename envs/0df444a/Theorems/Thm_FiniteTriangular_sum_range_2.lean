-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_2
-- name    : FiniteTriangular.sum_range_2
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:00:27.966468+00:00
-- url     : https://prove2.me/theorems/6b64402d-9727-4df6-b775-b58dbbf72e82
-- title:
--   Sum of integers below 2
-- statement:
--   The sum of the nonnegative integers strictly less than $2$ equals $1$. Equivalently, $\sum_{k=0}^{2-1} k = 2(2-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_2 : ∑ k ∈ range 2, k = 1 := by sorry

end FiniteTriangular
