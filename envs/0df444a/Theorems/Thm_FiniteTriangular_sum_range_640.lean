-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_640
-- name    : FiniteTriangular.sum_range_640
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:51:38.806376+00:00
-- url     : https://prove2.me/theorems/5c81b686-7cba-4c9d-8fda-976ac6e6a4b7
-- title:
--   Sum of integers below 640
-- statement:
--   The sum of the nonnegative integers strictly less than $640$ equals $204480$. Equivalently, $\\sum_{k=0}^{640-1} k = 640(640-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_640 : ∑ k ∈ range 640, k = 204480 := by sorry

end FiniteTriangular
