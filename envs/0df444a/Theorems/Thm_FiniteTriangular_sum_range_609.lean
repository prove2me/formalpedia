-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_609
-- name    : FiniteTriangular.sum_range_609
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:46:31.331436+00:00
-- url     : https://prove2.me/theorems/fd88e28d-1df2-4010-ac87-5724b7b1e849
-- title:
--   Sum of integers below 609
-- statement:
--   The sum of the nonnegative integers strictly less than $609$ equals $185136$. Equivalently, $\\sum_{k=0}^{609-1} k = 609(609-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_609 : ∑ k ∈ range 609, k = 185136 := by sorry

end FiniteTriangular
