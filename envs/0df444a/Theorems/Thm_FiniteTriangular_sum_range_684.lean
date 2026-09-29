-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_684
-- name    : FiniteTriangular.sum_range_684
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:01:49.650902+00:00
-- url     : https://prove2.me/theorems/081d2a48-cfc0-4f27-a2ed-351bb9353481
-- title:
--   Sum of integers below 684
-- statement:
--   The sum of the nonnegative integers strictly less than $684$ equals $233586$. Equivalently, $\\sum_{k=0}^{684-1} k = 684(684-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_684 : ∑ k ∈ range 684, k = 233586 := by sorry

end FiniteTriangular
