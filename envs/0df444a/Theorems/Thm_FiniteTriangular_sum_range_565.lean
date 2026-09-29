-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_565
-- name    : FiniteTriangular.sum_range_565
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:36:09.390467+00:00
-- url     : https://prove2.me/theorems/ac2b8042-3927-439d-ac78-ca1483d78499
-- title:
--   Sum of integers below 565
-- statement:
--   The sum of the nonnegative integers strictly less than $565$ equals $159330$. Equivalently, $\\sum_{k=0}^{565-1} k = 565(565-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_565 : ∑ k ∈ range 565, k = 159330 := by sorry

end FiniteTriangular
