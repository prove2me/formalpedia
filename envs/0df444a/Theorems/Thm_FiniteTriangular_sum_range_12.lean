-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_12
-- name    : FiniteTriangular.sum_range_12
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:03:47.518752+00:00
-- url     : https://prove2.me/theorems/bd95aac9-cf91-47d6-96d8-d90ae0d82991
-- title:
--   Sum of integers below 12
-- statement:
--   The sum of the nonnegative integers strictly less than $12$ equals $66$. Equivalently, $\sum_{k=0}^{12-1} k = 12(12-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_12 : ∑ k ∈ range 12, k = 66 := by sorry

end FiniteTriangular
