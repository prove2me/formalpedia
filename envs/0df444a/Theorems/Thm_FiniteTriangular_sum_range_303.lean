-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_303
-- name    : FiniteTriangular.sum_range_303
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T08:19:54.469455+00:00
-- url     : https://prove2.me/theorems/1710c3aa-7288-4ce8-9dca-7fa83cceab02
-- title:
--   Sum of integers below 303
-- statement:
--   The sum of the nonnegative integers strictly less than $303$ equals $45753$. Equivalently, $\\sum_{k=0}^{303-1} k = 303(303-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_303 : ∑ k ∈ range 303, k = 45753 := by sorry

end FiniteTriangular
