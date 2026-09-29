-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_126
-- name    : FiniteTriangular.sum_range_126
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:54:07.657283+00:00
-- url     : https://prove2.me/theorems/3266c973-9e62-4233-801b-2e5c4a5f3945
-- title:
--   Sum of integers below 126
-- statement:
--   The sum of the nonnegative integers strictly less than $126$ equals $7875$. Equivalently, $\sum_{k=0}^{126-1} k = 126(126-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_126 : ∑ k ∈ range 126, k = 7875 := by sorry

end FiniteTriangular
