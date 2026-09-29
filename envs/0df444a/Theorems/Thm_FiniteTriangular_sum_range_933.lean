-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_933
-- name    : FiniteTriangular.sum_range_933
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:55:13.720107+00:00
-- url     : https://prove2.me/theorems/eb9975d7-675a-4e2c-b7c6-d6ee375a9bef
-- title:
--   Sum of integers below 933
-- statement:
--   The sum of the nonnegative integers strictly less than $933$ equals $434778$. Equivalently, $\\sum_{k=0}^{933-1} k = 933(933-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_933 : ∑ k ∈ range 933, k = 434778 := by sorry

end FiniteTriangular
