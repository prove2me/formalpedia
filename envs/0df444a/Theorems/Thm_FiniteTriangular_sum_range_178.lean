-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_178
-- name    : FiniteTriangular.sum_range_178
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T20:04:04.515567+00:00
-- url     : https://prove2.me/theorems/14b98745-e8b3-4b90-a1f4-2a22744972a9
-- title:
--   Sum of integers below 178
-- statement:
--   The sum of the nonnegative integers strictly less than $178$ equals $15753$. Equivalently, $\sum_{k=0}^{178-1} k = 178(178-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_178 : ∑ k ∈ range 178, k = 15753 := by sorry

end FiniteTriangular
