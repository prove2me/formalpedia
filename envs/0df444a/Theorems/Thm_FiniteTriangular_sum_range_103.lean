-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_103
-- name    : FiniteTriangular.sum_range_103
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:45:27.836988+00:00
-- url     : https://prove2.me/theorems/aff7365b-65e8-4a2e-af4a-9e03067a1d77
-- title:
--   Sum of integers below 103
-- statement:
--   The sum of the nonnegative integers strictly less than $103$ equals $5253$. Equivalently, $\sum_{k=0}^{103-1} k = 103(103-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_103 : ∑ k ∈ range 103, k = 5253 := by sorry

end FiniteTriangular
