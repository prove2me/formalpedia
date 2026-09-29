-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_438
-- name    : FiniteTriangular.sum_range_438
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:57:27.859975+00:00
-- url     : https://prove2.me/theorems/ed7d0cca-f1e1-491e-90d3-11d44893e514
-- title:
--   Sum of integers below 438
-- statement:
--   The sum of the nonnegative integers strictly less than $438$ equals $95703$. Equivalently, $\\sum_{k=0}^{438-1} k = 438(438-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_438 : ∑ k ∈ range 438, k = 95703 := by sorry

end FiniteTriangular
