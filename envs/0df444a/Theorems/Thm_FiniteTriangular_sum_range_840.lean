-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_840
-- name    : FiniteTriangular.sum_range_840
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:35:10.900167+00:00
-- url     : https://prove2.me/theorems/8c2b7ff1-b326-445a-b21b-0b1cf50fd13e
-- title:
--   Sum of integers below 840
-- statement:
--   The sum of the nonnegative integers strictly less than $840$ equals $352380$. Equivalently, $\\sum_{k=0}^{840-1} k = 840(840-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_840 : ∑ k ∈ range 840, k = 352380 := by sorry

end FiniteTriangular
