-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_269
-- name    : FiniteTriangular.sum_range_269
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T08:12:49.116851+00:00
-- url     : https://prove2.me/theorems/c6c1d96c-cc4d-4569-ba15-d9cf877f363a
-- title:
--   Sum of integers below 269
-- statement:
--   The sum of the nonnegative integers strictly less than $269$ equals $36046$. Equivalently, $\\sum_{k=0}^{269-1} k = 269(269-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_269 : ∑ k ∈ range 269, k = 36046 := by sorry

end FiniteTriangular
