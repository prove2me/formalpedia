-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_957
-- name    : FiniteTriangular.sum_range_957
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T12:00:48.377838+00:00
-- url     : https://prove2.me/theorems/06b99f81-23c0-45e5-82de-1f54c7a6ed78
-- title:
--   Sum of integers below 957
-- statement:
--   The sum of the nonnegative integers strictly less than $957$ equals $457446$. Equivalently, $\\sum_{k=0}^{957-1} k = 957(957-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_957 : ∑ k ∈ range 957, k = 457446 := by sorry

end FiniteTriangular
