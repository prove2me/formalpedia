-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_846
-- name    : FiniteTriangular.sum_range_846
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:36:43.881206+00:00
-- url     : https://prove2.me/theorems/b6caccf4-42f1-47e1-9090-1d6abdad425b
-- title:
--   Sum of integers below 846
-- statement:
--   The sum of the nonnegative integers strictly less than $846$ equals $357435$. Equivalently, $\\sum_{k=0}^{846-1} k = 846(846-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_846 : ∑ k ∈ range 846, k = 357435 := by sorry

end FiniteTriangular
