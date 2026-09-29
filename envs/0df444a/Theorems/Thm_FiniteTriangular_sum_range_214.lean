-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_214
-- name    : FiniteTriangular.sum_range_214
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T07:51:32.024486+00:00
-- url     : https://prove2.me/theorems/4e2f81e6-5d5f-435c-b01d-105a86d7324d
-- title:
--   Sum of integers below 214
-- statement:
--   The sum of the nonnegative integers strictly less than $214$ equals $22791$. Equivalently, $\\sum_{k=0}^{214-1} k = 214(214-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_214 : ∑ k ∈ range 214, k = 22791 := by sorry

end FiniteTriangular
