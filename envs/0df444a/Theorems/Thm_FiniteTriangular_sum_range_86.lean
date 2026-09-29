-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_86
-- name    : FiniteTriangular.sum_range_86
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:40:02.824881+00:00
-- url     : https://prove2.me/theorems/7c54f24c-ddd1-4340-8a6d-02fc3cce86ce
-- title:
--   Sum of integers below 86
-- statement:
--   The sum of the nonnegative integers strictly less than $86$ equals $3655$. Equivalently, $\sum_{k=0}^{86-1} k = 86(86-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_86 : ∑ k ∈ range 86, k = 3655 := by sorry

end FiniteTriangular
