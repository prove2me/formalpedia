-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_560
-- name    : FiniteTriangular.sum_range_560
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:34:14.389347+00:00
-- url     : https://prove2.me/theorems/d731d1c0-19b8-43fa-b32b-2e2d12603176
-- title:
--   Sum of integers below 560
-- statement:
--   The sum of the nonnegative integers strictly less than $560$ equals $156520$. Equivalently, $\\sum_{k=0}^{560-1} k = 560(560-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_560 : ∑ k ∈ range 560, k = 156520 := by sorry

end FiniteTriangular
