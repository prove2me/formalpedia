-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_228
-- name    : FiniteTriangular.sum_range_228
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T07:55:03.317931+00:00
-- url     : https://prove2.me/theorems/a33ed7eb-4da8-437f-9f05-e3b50827aaa7
-- title:
--   Sum of integers below 228
-- statement:
--   The sum of the nonnegative integers strictly less than $228$ equals $25878$. Equivalently, $\\sum_{k=0}^{228-1} k = 228(228-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_228 : ∑ k ∈ range 228, k = 25878 := by sorry

end FiniteTriangular
