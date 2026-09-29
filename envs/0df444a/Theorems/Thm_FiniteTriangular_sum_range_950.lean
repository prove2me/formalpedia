-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_950
-- name    : FiniteTriangular.sum_range_950
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:58:55.624934+00:00
-- url     : https://prove2.me/theorems/25853f25-59c8-4898-9bc5-1f906e8d9e14
-- title:
--   Sum of integers below 950
-- statement:
--   The sum of the nonnegative integers strictly less than $950$ equals $450775$. Equivalently, $\\sum_{k=0}^{950-1} k = 950(950-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_950 : ∑ k ∈ range 950, k = 450775 := by sorry

end FiniteTriangular
