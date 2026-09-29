-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_21
-- name    : FiniteTriangular.sum_range_21
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:07:56.401914+00:00
-- url     : https://prove2.me/theorems/04142718-6113-4ee8-94ba-c3d9276d8392
-- title:
--   Sum of integers below 21
-- statement:
--   The sum of the nonnegative integers strictly less than $21$ equals $210$. Equivalently, $\sum_{k=0}^{21-1} k = 21(21-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_21 : ∑ k ∈ range 21, k = 210 := by sorry

end FiniteTriangular
