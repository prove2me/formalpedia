-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_173
-- name    : FiniteTriangular.sum_range_173
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T20:02:21.368438+00:00
-- url     : https://prove2.me/theorems/02cac349-c769-4a51-9b1b-248892485277
-- title:
--   Sum of integers below 173
-- statement:
--   The sum of the nonnegative integers strictly less than $173$ equals $14878$. Equivalently, $\sum_{k=0}^{173-1} k = 173(173-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_173 : ∑ k ∈ range 173, k = 14878 := by sorry

end FiniteTriangular
