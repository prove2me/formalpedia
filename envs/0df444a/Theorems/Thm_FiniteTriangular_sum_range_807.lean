-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_807
-- name    : FiniteTriangular.sum_range_807
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:28:10.409233+00:00
-- url     : https://prove2.me/theorems/178151ef-6eb7-49a5-bfd6-abf55bde2e7a
-- title:
--   Sum of integers below 807
-- statement:
--   The sum of the nonnegative integers strictly less than $807$ equals $325221$. Equivalently, $\\sum_{k=0}^{807-1} k = 807(807-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_807 : ∑ k ∈ range 807, k = 325221 := by sorry

end FiniteTriangular
