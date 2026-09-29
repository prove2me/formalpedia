-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_447
-- name    : FiniteTriangular.sum_range_447
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:08:03.996151+00:00
-- url     : https://prove2.me/theorems/849e6c34-92bf-4ee4-bf48-4c641d770d76
-- title:
--   Sum of integers below 447
-- statement:
--   The sum of the nonnegative integers strictly less than $447$ equals $99681$. Equivalently, $\\sum_{k=0}^{447-1} k = 447(447-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_447 : ∑ k ∈ range 447, k = 99681 := by sorry

end FiniteTriangular
