-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_770
-- name    : FiniteTriangular.sum_range_770
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:21:30.288857+00:00
-- url     : https://prove2.me/theorems/5d59e94d-23e7-4b12-bc3b-083a0ffc2730
-- title:
--   Sum of integers below 770
-- statement:
--   The sum of the nonnegative integers strictly less than $770$ equals $296065$. Equivalently, $\\sum_{k=0}^{770-1} k = 770(770-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_770 : ∑ k ∈ range 770, k = 296065 := by sorry

end FiniteTriangular
