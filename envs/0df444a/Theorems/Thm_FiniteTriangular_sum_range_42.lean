-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_42
-- name    : FiniteTriangular.sum_range_42
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:17:09.174978+00:00
-- url     : https://prove2.me/theorems/2e17558f-8a59-4444-a2e6-e7e78d11f882
-- title:
--   Sum of integers below 42
-- statement:
--   The sum of the nonnegative integers strictly less than $42$ equals $861$. Equivalently, $\sum_{k=0}^{42-1} k = 42(42-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_42 : ∑ k ∈ range 42, k = 861 := by sorry

end FiniteTriangular
