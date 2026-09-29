-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_436
-- name    : FiniteTriangular.sum_range_436
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:57:28.488409+00:00
-- url     : https://prove2.me/theorems/a3782995-67ab-457c-aac8-b90eef46dc6b
-- title:
--   Sum of integers below 436
-- statement:
--   The sum of the nonnegative integers strictly less than $436$ equals $94830$. Equivalently, $\\sum_{k=0}^{436-1} k = 436(436-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_436 : ∑ k ∈ range 436, k = 94830 := by sorry

end FiniteTriangular
