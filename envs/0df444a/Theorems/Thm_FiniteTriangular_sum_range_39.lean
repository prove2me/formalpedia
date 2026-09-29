-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_39
-- name    : FiniteTriangular.sum_range_39
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:14:58.916511+00:00
-- url     : https://prove2.me/theorems/63af5036-9661-4804-8f1e-c954ee5e7d66
-- title:
--   Sum of integers below 39
-- statement:
--   The sum of the nonnegative integers strictly less than $39$ equals $741$. Equivalently, $\sum_{k=0}^{39-1} k = 39(39-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_39 : ∑ k ∈ range 39, k = 741 := by sorry

end FiniteTriangular
