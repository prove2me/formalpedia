-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_128
-- name    : FiniteTriangular.sum_range_128
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:54:05.351383+00:00
-- url     : https://prove2.me/theorems/1b716981-8c99-49b1-a0ae-9d4f290eeed9
-- title:
--   Sum of integers below 128
-- statement:
--   The sum of the nonnegative integers strictly less than $128$ equals $8128$. Equivalently, $\sum_{k=0}^{128-1} k = 128(128-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_128 : ∑ k ∈ range 128, k = 8128 := by sorry

end FiniteTriangular
