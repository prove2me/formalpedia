-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_887
-- name    : FiniteTriangular.sum_range_887
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:45:11.136005+00:00
-- url     : https://prove2.me/theorems/00bd6450-2f13-4897-b77b-7d10f9c5df55
-- title:
--   Sum of integers below 887
-- statement:
--   The sum of the nonnegative integers strictly less than $887$ equals $392941$. Equivalently, $\\sum_{k=0}^{887-1} k = 887(887-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_887 : ∑ k ∈ range 887, k = 392941 := by sorry

end FiniteTriangular
