-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_83
-- name    : FiniteTriangular.sum_range_83
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:40:03.45444+00:00
-- url     : https://prove2.me/theorems/6ca8cfe4-bcad-422b-bcc2-2118ca5775a2
-- title:
--   Sum of integers below 83
-- statement:
--   The sum of the nonnegative integers strictly less than $83$ equals $3403$. Equivalently, $\sum_{k=0}^{83-1} k = 83(83-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_83 : ∑ k ∈ range 83, k = 3403 := by sorry

end FiniteTriangular
