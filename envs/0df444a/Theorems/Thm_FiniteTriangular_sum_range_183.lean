-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_183
-- name    : FiniteTriangular.sum_range_183
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T20:04:06.682124+00:00
-- url     : https://prove2.me/theorems/a196450f-70b7-402d-afca-db1dd09db630
-- title:
--   Sum of integers below 183
-- statement:
--   The sum of the nonnegative integers strictly less than $183$ equals $16653$. Equivalently, $\sum_{k=0}^{183-1} k = 183(183-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_183 : ∑ k ∈ range 183, k = 16653 := by sorry

end FiniteTriangular
