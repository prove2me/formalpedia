-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_241
-- name    : FiniteTriangular.sum_range_241
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T07:59:14.126341+00:00
-- url     : https://prove2.me/theorems/45d5a2f2-fe82-4e58-a3d2-bc80d3dc98c1
-- title:
--   Sum of integers below 241
-- statement:
--   The sum of the nonnegative integers strictly less than $241$ equals $28920$. Equivalently, $\\sum_{k=0}^{241-1} k = 241(241-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_241 : ∑ k ∈ range 241, k = 28920 := by sorry

end FiniteTriangular
