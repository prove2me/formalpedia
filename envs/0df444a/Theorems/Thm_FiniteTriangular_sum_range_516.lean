-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_516
-- name    : FiniteTriangular.sum_range_516
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:23:55.741188+00:00
-- url     : https://prove2.me/theorems/bd3a8a1f-e374-4c0f-8b51-63a0ac0e5784
-- title:
--   Sum of integers below 516
-- statement:
--   The sum of the nonnegative integers strictly less than $516$ equals $132870$. Equivalently, $\\sum_{k=0}^{516-1} k = 516(516-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_516 : ∑ k ∈ range 516, k = 132870 := by sorry

end FiniteTriangular
