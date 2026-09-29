-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_652
-- name    : FiniteTriangular.sum_range_652
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:54:48.726892+00:00
-- url     : https://prove2.me/theorems/4181873b-54e9-48bf-a0a3-3830024e2056
-- title:
--   Sum of integers below 652
-- statement:
--   The sum of the nonnegative integers strictly less than $652$ equals $212226$. Equivalently, $\\sum_{k=0}^{652-1} k = 652(652-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_652 : ∑ k ∈ range 652, k = 212226 := by sorry

end FiniteTriangular
