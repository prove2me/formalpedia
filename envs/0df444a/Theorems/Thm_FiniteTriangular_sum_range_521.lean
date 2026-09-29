-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_521
-- name    : FiniteTriangular.sum_range_521
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:25:40.607354+00:00
-- url     : https://prove2.me/theorems/21d65212-9c11-434c-8ab8-ba271a81b152
-- title:
--   Sum of integers below 521
-- statement:
--   The sum of the nonnegative integers strictly less than $521$ equals $135460$. Equivalently, $\\sum_{k=0}^{521-1} k = 521(521-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_521 : ∑ k ∈ range 521, k = 135460 := by sorry

end FiniteTriangular
