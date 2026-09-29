-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_49
-- name    : FiniteTriangular.sum_range_49
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:17:08.736411+00:00
-- url     : https://prove2.me/theorems/a9e7c2a3-805e-4683-8703-7722fb07adf3
-- title:
--   Sum of integers below 49
-- statement:
--   The sum of the nonnegative integers strictly less than $49$ equals $1176$. Equivalently, $\sum_{k=0}^{49-1} k = 49(49-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_49 : ∑ k ∈ range 49, k = 1176 := by sorry

end FiniteTriangular
