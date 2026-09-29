-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_478
-- name    : FiniteTriangular.sum_range_478
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:15:26.908307+00:00
-- url     : https://prove2.me/theorems/4a0c730e-a154-42c0-88e7-7bb1f97b3854
-- title:
--   Sum of integers below 478
-- statement:
--   The sum of the nonnegative integers strictly less than $478$ equals $114003$. Equivalently, $\\sum_{k=0}^{478-1} k = 478(478-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_478 : ∑ k ∈ range 478, k = 114003 := by sorry

end FiniteTriangular
