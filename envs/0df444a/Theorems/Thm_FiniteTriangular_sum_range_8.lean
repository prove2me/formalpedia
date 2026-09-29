-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_8
-- name    : FiniteTriangular.sum_range_8
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:00:49.725585+00:00
-- url     : https://prove2.me/theorems/7ffd5562-f7bb-4dd4-bb13-798c9f1cf741
-- title:
--   Sum of integers below 8
-- statement:
--   The sum of the nonnegative integers strictly less than $8$ equals $28$. Equivalently, $\sum_{k=0}^{8-1} k = 8(8-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_8 : ∑ k ∈ range 8, k = 28 := by sorry

end FiniteTriangular
