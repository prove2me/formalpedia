-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_343
-- name    : FiniteTriangular.sum_range_343
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:35:53.101878+00:00
-- url     : https://prove2.me/theorems/4de29b73-45cb-4d34-830b-19afd6224fc6
-- title:
--   Sum of integers below 343
-- statement:
--   The sum of the nonnegative integers strictly less than $343$ equals $58653$. Equivalently, $\\sum_{k=0}^{343-1} k = 343(343-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_343 : ∑ k ∈ range 343, k = 58653 := by sorry

end FiniteTriangular
