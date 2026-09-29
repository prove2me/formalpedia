-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_845
-- name    : FiniteTriangular.sum_range_845
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:36:44.22446+00:00
-- url     : https://prove2.me/theorems/b951a59f-5db3-4303-81ed-6ae5bcda944c
-- title:
--   Sum of integers below 845
-- statement:
--   The sum of the nonnegative integers strictly less than $845$ equals $356590$. Equivalently, $\\sum_{k=0}^{845-1} k = 845(845-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_845 : ∑ k ∈ range 845, k = 356590 := by sorry

end FiniteTriangular
