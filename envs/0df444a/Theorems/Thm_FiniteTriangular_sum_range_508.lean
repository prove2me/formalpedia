-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_508
-- name    : FiniteTriangular.sum_range_508
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:22:07.984452+00:00
-- url     : https://prove2.me/theorems/b3f0a2f6-af39-4254-a030-d677d865d3ed
-- title:
--   Sum of integers below 508
-- statement:
--   The sum of the nonnegative integers strictly less than $508$ equals $128778$. Equivalently, $\\sum_{k=0}^{508-1} k = 508(508-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_508 : ∑ k ∈ range 508, k = 128778 := by sorry

end FiniteTriangular
