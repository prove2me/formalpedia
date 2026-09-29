-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_490
-- name    : FiniteTriangular.sum_range_490
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:18:45.365433+00:00
-- url     : https://prove2.me/theorems/a1bb3e6a-cfeb-49f2-88c1-646f275502f2
-- title:
--   Sum of integers below 490
-- statement:
--   The sum of the nonnegative integers strictly less than $490$ equals $119805$. Equivalently, $\\sum_{k=0}^{490-1} k = 490(490-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_490 : ∑ k ∈ range 490, k = 119805 := by sorry

end FiniteTriangular
