-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_94
-- name    : FiniteTriangular.sum_range_94
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:43:44.085746+00:00
-- url     : https://prove2.me/theorems/878f7d0e-5a6c-4b75-be28-1d002bdc7ffe
-- title:
--   Sum of integers below 94
-- statement:
--   The sum of the nonnegative integers strictly less than $94$ equals $4371$. Equivalently, $\sum_{k=0}^{94-1} k = 94(94-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_94 : ∑ k ∈ range 94, k = 4371 := by sorry

end FiniteTriangular
