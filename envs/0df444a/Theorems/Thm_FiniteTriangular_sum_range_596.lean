-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_596
-- name    : FiniteTriangular.sum_range_596
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:43:01.347238+00:00
-- url     : https://prove2.me/theorems/8522ff9d-f2da-4cd6-b3ba-02abc1175d4c
-- title:
--   Sum of integers below 596
-- statement:
--   The sum of the nonnegative integers strictly less than $596$ equals $177310$. Equivalently, $\\sum_{k=0}^{596-1} k = 596(596-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_596 : ∑ k ∈ range 596, k = 177310 := by sorry

end FiniteTriangular
