-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_736
-- name    : FiniteTriangular.sum_range_736
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:12:32.247178+00:00
-- url     : https://prove2.me/theorems/f83fc276-4847-45ca-9914-45e1fa5db783
-- title:
--   Sum of integers below 736
-- statement:
--   The sum of the nonnegative integers strictly less than $736$ equals $270480$. Equivalently, $\\sum_{k=0}^{736-1} k = 736(736-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_736 : ∑ k ∈ range 736, k = 270480 := by sorry

end FiniteTriangular
