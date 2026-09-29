-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_365
-- name    : FiniteTriangular.sum_range_365
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:41:16.594756+00:00
-- url     : https://prove2.me/theorems/0dc87286-1294-4f84-8f5b-57ec939d36fa
-- title:
--   Sum of integers below 365
-- statement:
--   The sum of the nonnegative integers strictly less than $365$ equals $66430$. Equivalently, $\\sum_{k=0}^{365-1} k = 365(365-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_365 : ∑ k ∈ range 365, k = 66430 := by sorry

end FiniteTriangular
