-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_175
-- name    : FiniteTriangular.sum_range_175
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T20:02:18.922871+00:00
-- url     : https://prove2.me/theorems/745e8706-bcb8-4017-88a8-862568626356
-- title:
--   Sum of integers below 175
-- statement:
--   The sum of the nonnegative integers strictly less than $175$ equals $15225$. Equivalently, $\sum_{k=0}^{175-1} k = 175(175-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_175 : ∑ k ∈ range 175, k = 15225 := by sorry

end FiniteTriangular
