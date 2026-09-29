-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_153
-- name    : FiniteTriangular.sum_range_153
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:59:22.695746+00:00
-- url     : https://prove2.me/theorems/fd11d679-70f6-4558-95f0-b43dd6b33703
-- title:
--   Sum of integers below 153
-- statement:
--   The sum of the nonnegative integers strictly less than $153$ equals $11628$. Equivalently, $\sum_{k=0}^{153-1} k = 153(153-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_153 : ∑ k ∈ range 153, k = 11628 := by sorry

end FiniteTriangular
