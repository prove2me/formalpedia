-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_618
-- name    : FiniteTriangular.sum_range_618
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:48:10.234987+00:00
-- url     : https://prove2.me/theorems/ea7d7f0b-74a3-4cec-b418-771f5088f641
-- title:
--   Sum of integers below 618
-- statement:
--   The sum of the nonnegative integers strictly less than $618$ equals $190653$. Equivalently, $\\sum_{k=0}^{618-1} k = 618(618-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_618 : ∑ k ∈ range 618, k = 190653 := by sorry

end FiniteTriangular
