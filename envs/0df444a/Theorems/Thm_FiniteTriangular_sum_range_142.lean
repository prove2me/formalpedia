-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_142
-- name    : FiniteTriangular.sum_range_142
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:57:01.66203+00:00
-- url     : https://prove2.me/theorems/7a45ae1d-fe60-4f78-9376-ba98b2a2d9d1
-- title:
--   Sum of integers below 142
-- statement:
--   The sum of the nonnegative integers strictly less than $142$ equals $10011$. Equivalently, $\sum_{k=0}^{142-1} k = 142(142-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_142 : ∑ k ∈ range 142, k = 10011 := by sorry

end FiniteTriangular
