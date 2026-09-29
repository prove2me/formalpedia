-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_82
-- name    : FiniteTriangular.sum_range_82
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:39:59.185674+00:00
-- url     : https://prove2.me/theorems/ad03a7ef-23af-4126-b544-97e6515bd3be
-- title:
--   Sum of integers below 82
-- statement:
--   The sum of the nonnegative integers strictly less than $82$ equals $3321$. Equivalently, $\sum_{k=0}^{82-1} k = 82(82-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_82 : ∑ k ∈ range 82, k = 3321 := by sorry

end FiniteTriangular
