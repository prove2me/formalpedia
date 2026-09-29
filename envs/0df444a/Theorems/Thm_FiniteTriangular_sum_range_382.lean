-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_382
-- name    : FiniteTriangular.sum_range_382
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:45:14.484032+00:00
-- url     : https://prove2.me/theorems/6b1aa4d2-3d4d-41c0-bfa4-06fce39b141c
-- title:
--   Sum of integers below 382
-- statement:
--   The sum of the nonnegative integers strictly less than $382$ equals $72771$. Equivalently, $\\sum_{k=0}^{382-1} k = 382(382-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_382 : ∑ k ∈ range 382, k = 72771 := by sorry

end FiniteTriangular
