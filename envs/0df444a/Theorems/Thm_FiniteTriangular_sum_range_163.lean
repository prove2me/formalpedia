-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_163
-- name    : FiniteTriangular.sum_range_163
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T20:00:50.66248+00:00
-- url     : https://prove2.me/theorems/81216988-194c-4a13-a5fb-8f05a038e39e
-- title:
--   Sum of integers below 163
-- statement:
--   The sum of the nonnegative integers strictly less than $163$ equals $13203$. Equivalently, $\sum_{k=0}^{163-1} k = 163(163-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_163 : ∑ k ∈ range 163, k = 13203 := by sorry

end FiniteTriangular
