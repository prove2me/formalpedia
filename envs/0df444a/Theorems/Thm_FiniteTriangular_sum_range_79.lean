-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_79
-- name    : FiniteTriangular.sum_range_79
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:38:10.037899+00:00
-- url     : https://prove2.me/theorems/b735193b-7fce-4997-b06f-446e4c313fd1
-- title:
--   Sum of integers below 79
-- statement:
--   The sum of the nonnegative integers strictly less than $79$ equals $3081$. Equivalently, $\sum_{k=0}^{79-1} k = 79(79-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_79 : ∑ k ∈ range 79, k = 3081 := by sorry

end FiniteTriangular
