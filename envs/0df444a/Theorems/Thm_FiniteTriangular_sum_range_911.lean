-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_911
-- name    : FiniteTriangular.sum_range_911
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:50:13.067294+00:00
-- url     : https://prove2.me/theorems/49faad58-5044-4c81-b978-2e60ea8505b7
-- title:
--   Sum of integers below 911
-- statement:
--   The sum of the nonnegative integers strictly less than $911$ equals $414505$. Equivalently, $\\sum_{k=0}^{911-1} k = 911(911-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_911 : ∑ k ∈ range 911, k = 414505 := by sorry

end FiniteTriangular
