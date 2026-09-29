-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_242
-- name    : FiniteTriangular.sum_range_242
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T07:59:16.241654+00:00
-- url     : https://prove2.me/theorems/1367f71a-4577-4f26-a418-62bc809bae2f
-- title:
--   Sum of integers below 242
-- statement:
--   The sum of the nonnegative integers strictly less than $242$ equals $29161$. Equivalently, $\\sum_{k=0}^{242-1} k = 242(242-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_242 : ∑ k ∈ range 242, k = 29161 := by sorry

end FiniteTriangular
