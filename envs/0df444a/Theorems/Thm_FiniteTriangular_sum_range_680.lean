-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_680
-- name    : FiniteTriangular.sum_range_680
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:00:00.742834+00:00
-- url     : https://prove2.me/theorems/7e91d360-fcf0-4534-8dbb-922f78c7ef98
-- title:
--   Sum of integers below 680
-- statement:
--   The sum of the nonnegative integers strictly less than $680$ equals $230860$. Equivalently, $\\sum_{k=0}^{680-1} k = 680(680-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_680 : ∑ k ∈ range 680, k = 230860 := by sorry

end FiniteTriangular
