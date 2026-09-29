-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_771
-- name    : FiniteTriangular.sum_range_771
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:21:25.792607+00:00
-- url     : https://prove2.me/theorems/e5a3484a-a432-4159-9a52-5d1326600bba
-- title:
--   Sum of integers below 771
-- statement:
--   The sum of the nonnegative integers strictly less than $771$ equals $296835$. Equivalently, $\\sum_{k=0}^{771-1} k = 771(771-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_771 : ∑ k ∈ range 771, k = 296835 := by sorry

end FiniteTriangular
