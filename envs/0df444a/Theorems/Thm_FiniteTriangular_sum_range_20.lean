-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_20
-- name    : FiniteTriangular.sum_range_20
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:07:53.804186+00:00
-- url     : https://prove2.me/theorems/23cf2719-eb99-4131-945b-7a2dee962aeb
-- title:
--   Sum of integers below 20
-- statement:
--   The sum of the nonnegative integers strictly less than $20$ equals $190$. Equivalently, $\sum_{k=0}^{20-1} k = 20(20-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_20 : ∑ k ∈ range 20, k = 190 := by sorry

end FiniteTriangular
