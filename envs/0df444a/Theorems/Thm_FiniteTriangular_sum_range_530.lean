-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_530
-- name    : FiniteTriangular.sum_range_530
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:27:15.800192+00:00
-- url     : https://prove2.me/theorems/ad4e580d-1b2e-43f3-a89b-1bc137f856a1
-- title:
--   Sum of integers below 530
-- statement:
--   The sum of the nonnegative integers strictly less than $530$ equals $140185$. Equivalently, $\\sum_{k=0}^{530-1} k = 530(530-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_530 : ∑ k ∈ range 530, k = 140185 := by sorry

end FiniteTriangular
