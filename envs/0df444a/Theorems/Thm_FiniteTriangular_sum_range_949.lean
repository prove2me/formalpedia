-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_949
-- name    : FiniteTriangular.sum_range_949
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:58:54.976575+00:00
-- url     : https://prove2.me/theorems/d9e2d8a5-6bb5-46f5-86da-9dd497d3b49d
-- title:
--   Sum of integers below 949
-- statement:
--   The sum of the nonnegative integers strictly less than $949$ equals $449826$. Equivalently, $\\sum_{k=0}^{949-1} k = 949(949-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_949 : ∑ k ∈ range 949, k = 449826 := by sorry

end FiniteTriangular
