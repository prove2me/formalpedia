-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_607
-- name    : FiniteTriangular.sum_range_607
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:44:42.009053+00:00
-- url     : https://prove2.me/theorems/60054f59-efb7-4325-acf3-8e78302e27c8
-- title:
--   Sum of integers below 607
-- statement:
--   The sum of the nonnegative integers strictly less than $607$ equals $183921$. Equivalently, $\\sum_{k=0}^{607-1} k = 607(607-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_607 : ∑ k ∈ range 607, k = 183921 := by sorry

end FiniteTriangular
