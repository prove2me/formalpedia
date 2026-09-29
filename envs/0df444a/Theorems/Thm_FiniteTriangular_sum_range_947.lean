-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_947
-- name    : FiniteTriangular.sum_range_947
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:58:55.516522+00:00
-- url     : https://prove2.me/theorems/cf6d80a2-a8fb-408b-8a83-e1719676d0d9
-- title:
--   Sum of integers below 947
-- statement:
--   The sum of the nonnegative integers strictly less than $947$ equals $447931$. Equivalently, $\\sum_{k=0}^{947-1} k = 947(947-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_947 : ∑ k ∈ range 947, k = 447931 := by sorry

end FiniteTriangular
