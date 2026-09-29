-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_476
-- name    : FiniteTriangular.sum_range_476
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:15:28.006739+00:00
-- url     : https://prove2.me/theorems/3824929b-a786-4290-8097-f6aa1d86153f
-- title:
--   Sum of integers below 476
-- statement:
--   The sum of the nonnegative integers strictly less than $476$ equals $113050$. Equivalently, $\\sum_{k=0}^{476-1} k = 476(476-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_476 : ∑ k ∈ range 476, k = 113050 := by sorry

end FiniteTriangular
