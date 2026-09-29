-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_375
-- name    : FiniteTriangular.sum_range_375
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:43:08.762797+00:00
-- url     : https://prove2.me/theorems/c12b63f6-99f1-443a-a62e-6c57bd99a5c1
-- title:
--   Sum of integers below 375
-- statement:
--   The sum of the nonnegative integers strictly less than $375$ equals $70125$. Equivalently, $\\sum_{k=0}^{375-1} k = 375(375-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_375 : ∑ k ∈ range 375, k = 70125 := by sorry

end FiniteTriangular
