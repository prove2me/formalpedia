-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_839
-- name    : FiniteTriangular.sum_range_839
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:35:10.330663+00:00
-- url     : https://prove2.me/theorems/b1d1aab0-b516-4a75-a334-0556b782ed5e
-- title:
--   Sum of integers below 839
-- statement:
--   The sum of the nonnegative integers strictly less than $839$ equals $351541$. Equivalently, $\\sum_{k=0}^{839-1} k = 839(839-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_839 : ∑ k ∈ range 839, k = 351541 := by sorry

end FiniteTriangular
