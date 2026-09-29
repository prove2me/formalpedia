-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_452
-- name    : FiniteTriangular.sum_range_452
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:09:50.632598+00:00
-- url     : https://prove2.me/theorems/204fadd2-d180-4d9f-b732-134ac4d204d6
-- title:
--   Sum of integers below 452
-- statement:
--   The sum of the nonnegative integers strictly less than $452$ equals $101926$. Equivalently, $\\sum_{k=0}^{452-1} k = 452(452-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_452 : ∑ k ∈ range 452, k = 101926 := by sorry

end FiniteTriangular
