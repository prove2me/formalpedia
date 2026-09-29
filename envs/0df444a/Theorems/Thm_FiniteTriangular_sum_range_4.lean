-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_4
-- name    : FiniteTriangular.sum_range_4
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:00:35.552499+00:00
-- url     : https://prove2.me/theorems/71b2943a-b897-4f6b-933e-a7266498a72d
-- title:
--   Sum of integers below 4
-- statement:
--   The sum of the nonnegative integers strictly less than $4$ equals $6$. Equivalently, $\sum_{k=0}^{4-1} k = 4(4-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_4 : ∑ k ∈ range 4, k = 6 := by sorry

end FiniteTriangular
