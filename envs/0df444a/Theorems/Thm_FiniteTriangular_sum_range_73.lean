-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_73
-- name    : FiniteTriangular.sum_range_73
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:38:06.347431+00:00
-- url     : https://prove2.me/theorems/61a0cb3b-9f13-43bf-80c6-9741518aac4d
-- title:
--   Sum of integers below 73
-- statement:
--   The sum of the nonnegative integers strictly less than $73$ equals $2628$. Equivalently, $\sum_{k=0}^{73-1} k = 73(73-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_73 : ∑ k ∈ range 73, k = 2628 := by sorry

end FiniteTriangular
