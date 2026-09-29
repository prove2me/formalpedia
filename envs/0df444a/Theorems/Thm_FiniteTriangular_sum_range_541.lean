-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_541
-- name    : FiniteTriangular.sum_range_541
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:28:56.389724+00:00
-- url     : https://prove2.me/theorems/2f41efbc-aa4e-4e39-bb7e-28adb26db671
-- title:
--   Sum of integers below 541
-- statement:
--   The sum of the nonnegative integers strictly less than $541$ equals $146070$. Equivalently, $\\sum_{k=0}^{541-1} k = 541(541-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_541 : ∑ k ∈ range 541, k = 146070 := by sorry

end FiniteTriangular
