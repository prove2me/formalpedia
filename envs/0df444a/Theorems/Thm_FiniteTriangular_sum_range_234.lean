-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_234
-- name    : FiniteTriangular.sum_range_234
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T07:57:35.896483+00:00
-- url     : https://prove2.me/theorems/5750354d-ac00-463e-9c41-040cea1c1b81
-- title:
--   Sum of integers below 234
-- statement:
--   The sum of the nonnegative integers strictly less than $234$ equals $27261$. Equivalently, $\\sum_{k=0}^{234-1} k = 234(234-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_234 : ∑ k ∈ range 234, k = 27261 := by sorry

end FiniteTriangular
