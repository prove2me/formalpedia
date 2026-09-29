-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_162
-- name    : FiniteTriangular.sum_range_162
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T20:00:48.745756+00:00
-- url     : https://prove2.me/theorems/2c395cd7-32eb-4880-97da-3c74d3adab37
-- title:
--   Sum of integers below 162
-- statement:
--   The sum of the nonnegative integers strictly less than $162$ equals $13041$. Equivalently, $\sum_{k=0}^{162-1} k = 162(162-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_162 : ∑ k ∈ range 162, k = 13041 := by sorry

end FiniteTriangular
