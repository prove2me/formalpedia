-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_605
-- name    : FiniteTriangular.sum_range_605
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:44:43.313048+00:00
-- url     : https://prove2.me/theorems/aeb9a733-1030-4209-b895-9231f907f8d7
-- title:
--   Sum of integers below 605
-- statement:
--   The sum of the nonnegative integers strictly less than $605$ equals $182710$. Equivalently, $\\sum_{k=0}^{605-1} k = 605(605-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_605 : ∑ k ∈ range 605, k = 182710 := by sorry

end FiniteTriangular
