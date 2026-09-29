-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_10
-- name    : FiniteTriangular.sum_range_10
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:03:46.020764+00:00
-- url     : https://prove2.me/theorems/37e94d57-424a-4b93-8186-4be82011db33
-- title:
--   Sum of integers below 10
-- statement:
--   The sum of the nonnegative integers strictly less than $10$ equals $45$. Equivalently, $\sum_{k=0}^{10-1} k = 10(10-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_10 : ∑ k ∈ range 10, k = 45 := by sorry

end FiniteTriangular
