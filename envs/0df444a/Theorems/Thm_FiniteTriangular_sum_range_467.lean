-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_467
-- name    : FiniteTriangular.sum_range_467
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:13:38.11075+00:00
-- url     : https://prove2.me/theorems/9e4d491c-2be6-452a-9ead-10af6ae2a2e6
-- title:
--   Sum of integers below 467
-- statement:
--   The sum of the nonnegative integers strictly less than $467$ equals $108811$. Equivalently, $\\sum_{k=0}^{467-1} k = 467(467-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_467 : ∑ k ∈ range 467, k = 108811 := by sorry

end FiniteTriangular
