-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_97
-- name    : FiniteTriangular.sum_range_97
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:45:22.251992+00:00
-- url     : https://prove2.me/theorems/29dff4ea-c222-4d94-a249-7b001787cbd8
-- title:
--   Sum of integers below 97
-- statement:
--   The sum of the nonnegative integers strictly less than $97$ equals $4656$. Equivalently, $\sum_{k=0}^{97-1} k = 97(97-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_97 : ∑ k ∈ range 97, k = 4656 := by sorry

end FiniteTriangular
