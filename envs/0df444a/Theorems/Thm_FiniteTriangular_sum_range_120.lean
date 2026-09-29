-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_120
-- name    : FiniteTriangular.sum_range_120
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:49:08.773126+00:00
-- url     : https://prove2.me/theorems/b2a8c153-074d-4726-9309-879daaa2b650
-- title:
--   Sum of integers below 120
-- statement:
--   The sum of the nonnegative integers strictly less than $120$ equals $7140$. Equivalently, $\sum_{k=0}^{120-1} k = 120(120-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_120 : ∑ k ∈ range 120, k = 7140 := by sorry

end FiniteTriangular
