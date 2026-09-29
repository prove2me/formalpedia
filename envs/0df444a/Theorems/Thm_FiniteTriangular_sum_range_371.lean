-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_371
-- name    : FiniteTriangular.sum_range_371
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:43:06.58024+00:00
-- url     : https://prove2.me/theorems/0ba8f28a-fdd7-4947-9558-fd48fc3672c7
-- title:
--   Sum of integers below 371
-- statement:
--   The sum of the nonnegative integers strictly less than $371$ equals $68635$. Equivalently, $\\sum_{k=0}^{371-1} k = 371(371-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_371 : ∑ k ∈ range 371, k = 68635 := by sorry

end FiniteTriangular
