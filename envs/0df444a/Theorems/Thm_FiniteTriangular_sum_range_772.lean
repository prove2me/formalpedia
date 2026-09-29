-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_772
-- name    : FiniteTriangular.sum_range_772
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:21:32.342451+00:00
-- url     : https://prove2.me/theorems/744dfde7-f470-4182-ab39-f9bb9a93ddff
-- title:
--   Sum of integers below 772
-- statement:
--   The sum of the nonnegative integers strictly less than $772$ equals $297606$. Equivalently, $\\sum_{k=0}^{772-1} k = 772(772-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_772 : ∑ k ∈ range 772, k = 297606 := by sorry

end FiniteTriangular
