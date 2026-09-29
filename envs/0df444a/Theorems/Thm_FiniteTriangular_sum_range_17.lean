-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_17
-- name    : FiniteTriangular.sum_range_17
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:04:01.643657+00:00
-- url     : https://prove2.me/theorems/f3280ee3-9577-402c-b052-5ccad6f6dc7d
-- title:
--   Sum of integers below 17
-- statement:
--   The sum of the nonnegative integers strictly less than $17$ equals $136$. Equivalently, $\sum_{k=0}^{17-1} k = 17(17-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_17 : ∑ k ∈ range 17, k = 136 := by sorry

end FiniteTriangular
