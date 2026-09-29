-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_6
-- name    : FiniteTriangular.sum_range_6
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:00:42.788366+00:00
-- url     : https://prove2.me/theorems/9ffef970-9d5c-426c-8932-58dfa8532772
-- title:
--   Sum of integers below 6
-- statement:
--   The sum of the nonnegative integers strictly less than $6$ equals $15$. Equivalently, $\sum_{k=0}^{6-1} k = 6(6-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_6 : ∑ k ∈ range 6, k = 15 := by sorry

end FiniteTriangular
