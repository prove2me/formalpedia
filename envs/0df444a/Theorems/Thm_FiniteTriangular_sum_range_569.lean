-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_569
-- name    : FiniteTriangular.sum_range_569
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:37:45.113901+00:00
-- url     : https://prove2.me/theorems/5be8ceb7-cae0-4768-8bd8-26a7e505778b
-- title:
--   Sum of integers below 569
-- statement:
--   The sum of the nonnegative integers strictly less than $569$ equals $161596$. Equivalently, $\\sum_{k=0}^{569-1} k = 569(569-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_569 : ∑ k ∈ range 569, k = 161596 := by sorry

end FiniteTriangular
