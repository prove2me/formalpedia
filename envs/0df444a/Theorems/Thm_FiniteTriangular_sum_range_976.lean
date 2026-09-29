-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_976
-- name    : FiniteTriangular.sum_range_976
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T12:04:14.932557+00:00
-- url     : https://prove2.me/theorems/bb1b37ed-34a0-42c7-9874-c0b5a6145685
-- title:
--   Sum of integers below 976
-- statement:
--   The sum of the nonnegative integers strictly less than $976$ equals $475800$. Equivalently, $\\sum_{k=0}^{976-1} k = 976(976-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_976 : ∑ k ∈ range 976, k = 475800 := by sorry

end FiniteTriangular
