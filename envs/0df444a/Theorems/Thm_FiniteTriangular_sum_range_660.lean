-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_660
-- name    : FiniteTriangular.sum_range_660
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:56:38.702221+00:00
-- url     : https://prove2.me/theorems/4735d8c2-040f-4f52-8302-5b3bc333f0fa
-- title:
--   Sum of integers below 660
-- statement:
--   The sum of the nonnegative integers strictly less than $660$ equals $217470$. Equivalently, $\\sum_{k=0}^{660-1} k = 660(660-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_660 : ∑ k ∈ range 660, k = 217470 := by sorry

end FiniteTriangular
