-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_324
-- name    : FiniteTriangular.sum_range_324
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:32:10.671983+00:00
-- url     : https://prove2.me/theorems/85c16ee0-b72d-4c03-b664-9eaa70dae037
-- title:
--   Sum of integers below 324
-- statement:
--   The sum of the nonnegative integers strictly less than $324$ equals $52326$. Equivalently, $\\sum_{k=0}^{324-1} k = 324(324-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_324 : ∑ k ∈ range 324, k = 52326 := by sorry

end FiniteTriangular
