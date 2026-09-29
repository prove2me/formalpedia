-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_905
-- name    : FiniteTriangular.sum_range_905
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:50:15.23405+00:00
-- url     : https://prove2.me/theorems/513c71c4-22ec-46e8-8203-6786336d0f58
-- title:
--   Sum of integers below 905
-- statement:
--   The sum of the nonnegative integers strictly less than $905$ equals $409060$. Equivalently, $\\sum_{k=0}^{905-1} k = 905(905-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_905 : ∑ k ∈ range 905, k = 409060 := by sorry

end FiniteTriangular
