-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_118
-- name    : FiniteTriangular.sum_range_118
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:49:08.078723+00:00
-- url     : https://prove2.me/theorems/64f4adae-b052-4b69-a18c-bd2e32b95226
-- title:
--   Sum of integers below 118
-- statement:
--   The sum of the nonnegative integers strictly less than $118$ equals $6903$. Equivalently, $\sum_{k=0}^{118-1} k = 118(118-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_118 : ∑ k ∈ range 118, k = 6903 := by sorry

end FiniteTriangular
