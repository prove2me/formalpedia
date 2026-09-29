-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_831
-- name    : FiniteTriangular.sum_range_831
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:33:31.437873+00:00
-- url     : https://prove2.me/theorems/cd863f0d-bce4-4a2d-a71e-37d89a0df071
-- title:
--   Sum of integers below 831
-- statement:
--   The sum of the nonnegative integers strictly less than $831$ equals $344865$. Equivalently, $\\sum_{k=0}^{831-1} k = 831(831-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_831 : ∑ k ∈ range 831, k = 344865 := by sorry

end FiniteTriangular
