-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_543
-- name    : FiniteTriangular.sum_range_543
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:28:55.706658+00:00
-- url     : https://prove2.me/theorems/1701dfe8-f131-4975-b8a1-b315b945d403
-- title:
--   Sum of integers below 543
-- statement:
--   The sum of the nonnegative integers strictly less than $543$ equals $147153$. Equivalently, $\\sum_{k=0}^{543-1} k = 543(543-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_543 : ∑ k ∈ range 543, k = 147153 := by sorry

end FiniteTriangular
