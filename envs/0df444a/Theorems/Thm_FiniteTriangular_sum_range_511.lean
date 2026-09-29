-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_511
-- name    : FiniteTriangular.sum_range_511
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:22:11.740022+00:00
-- url     : https://prove2.me/theorems/24df2e87-583a-42e8-b4ba-017a2bd67dc1
-- title:
--   Sum of integers below 511
-- statement:
--   The sum of the nonnegative integers strictly less than $511$ equals $130305$. Equivalently, $\\sum_{k=0}^{511-1} k = 511(511-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_511 : ∑ k ∈ range 511, k = 130305 := by sorry

end FiniteTriangular
