-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_410
-- name    : FiniteTriangular.sum_range_410
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:52:06.493457+00:00
-- url     : https://prove2.me/theorems/8bb351e7-7ad9-4551-87ec-4a529d8ad961
-- title:
--   Sum of integers below 410
-- statement:
--   The sum of the nonnegative integers strictly less than $410$ equals $83845$. Equivalently, $\\sum_{k=0}^{410-1} k = 410(410-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_410 : ∑ k ∈ range 410, k = 83845 := by sorry

end FiniteTriangular
