-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_268
-- name    : FiniteTriangular.sum_range_268
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T08:12:50.00148+00:00
-- url     : https://prove2.me/theorems/b618a4a7-703d-459d-a0d6-de7273f5e6c4
-- title:
--   Sum of integers below 268
-- statement:
--   The sum of the nonnegative integers strictly less than $268$ equals $35778$. Equivalently, $\\sum_{k=0}^{268-1} k = 268(268-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_268 : ∑ k ∈ range 268, k = 35778 := by sorry

end FiniteTriangular
