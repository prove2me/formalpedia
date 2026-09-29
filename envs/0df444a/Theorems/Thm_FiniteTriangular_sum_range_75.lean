-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_75
-- name    : FiniteTriangular.sum_range_75
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:38:09.812977+00:00
-- url     : https://prove2.me/theorems/ee81c63b-d2d7-4e37-9a0b-425f86c962e8
-- title:
--   Sum of integers below 75
-- statement:
--   The sum of the nonnegative integers strictly less than $75$ equals $2775$. Equivalently, $\sum_{k=0}^{75-1} k = 75(75-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_75 : ∑ k ∈ range 75, k = 2775 := by sorry

end FiniteTriangular
