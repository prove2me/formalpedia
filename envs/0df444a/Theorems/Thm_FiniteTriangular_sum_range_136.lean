-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_136
-- name    : FiniteTriangular.sum_range_136
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:55:52.234889+00:00
-- url     : https://prove2.me/theorems/bc3407d4-0d01-4d7f-93cd-1fe795c3759b
-- title:
--   Sum of integers below 136
-- statement:
--   The sum of the nonnegative integers strictly less than $136$ equals $9180$. Equivalently, $\sum_{k=0}^{136-1} k = 136(136-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_136 : ∑ k ∈ range 136, k = 9180 := by sorry

end FiniteTriangular
