-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_388
-- name    : FiniteTriangular.sum_range_388
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:46:58.068582+00:00
-- url     : https://prove2.me/theorems/11a71416-d742-43d7-a8e2-bf9103ced00a
-- title:
--   Sum of integers below 388
-- statement:
--   The sum of the nonnegative integers strictly less than $388$ equals $75078$. Equivalently, $\\sum_{k=0}^{388-1} k = 388(388-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_388 : ∑ k ∈ range 388, k = 75078 := by sorry

end FiniteTriangular
