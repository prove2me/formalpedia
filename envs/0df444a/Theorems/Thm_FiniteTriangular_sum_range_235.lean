-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_235
-- name    : FiniteTriangular.sum_range_235
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T07:57:34.993788+00:00
-- url     : https://prove2.me/theorems/63d1371c-f3ab-44bc-bbf3-e720dc56fb9c
-- title:
--   Sum of integers below 235
-- statement:
--   The sum of the nonnegative integers strictly less than $235$ equals $27495$. Equivalently, $\\sum_{k=0}^{235-1} k = 235(235-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_235 : ∑ k ∈ range 235, k = 27495 := by sorry

end FiniteTriangular
