-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_688
-- name    : FiniteTriangular.sum_range_688
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:01:48.725436+00:00
-- url     : https://prove2.me/theorems/28d2e4c4-9575-4846-b252-3c488cee923c
-- title:
--   Sum of integers below 688
-- statement:
--   The sum of the nonnegative integers strictly less than $688$ equals $236328$. Equivalently, $\\sum_{k=0}^{688-1} k = 688(688-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_688 : ∑ k ∈ range 688, k = 236328 := by sorry

end FiniteTriangular
