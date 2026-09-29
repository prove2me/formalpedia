-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_374
-- name    : FiniteTriangular.sum_range_374
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:43:07.901153+00:00
-- url     : https://prove2.me/theorems/8975b1e8-eae8-4cc6-b28f-80d9aafae7ae
-- title:
--   Sum of integers below 374
-- statement:
--   The sum of the nonnegative integers strictly less than $374$ equals $69751$. Equivalently, $\\sum_{k=0}^{374-1} k = 374(374-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_374 : ∑ k ∈ range 374, k = 69751 := by sorry

end FiniteTriangular
