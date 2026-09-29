-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_167
-- name    : FiniteTriangular.sum_range_167
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T20:00:50.533719+00:00
-- url     : https://prove2.me/theorems/ca6e6ad5-843f-4971-8dca-1fff09a96e39
-- title:
--   Sum of integers below 167
-- statement:
--   The sum of the nonnegative integers strictly less than $167$ equals $13861$. Equivalently, $\sum_{k=0}^{167-1} k = 167(167-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_167 : ∑ k ∈ range 167, k = 13861 := by sorry

end FiniteTriangular
