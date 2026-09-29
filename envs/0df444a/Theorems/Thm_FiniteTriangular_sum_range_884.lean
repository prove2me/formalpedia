-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_884
-- name    : FiniteTriangular.sum_range_884
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:45:09.178728+00:00
-- url     : https://prove2.me/theorems/e07af8bd-6d31-44d7-ba72-13eb952dd5cc
-- title:
--   Sum of integers below 884
-- statement:
--   The sum of the nonnegative integers strictly less than $884$ equals $390286$. Equivalently, $\\sum_{k=0}^{884-1} k = 884(884-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_884 : ∑ k ∈ range 884, k = 390286 := by sorry

end FiniteTriangular
