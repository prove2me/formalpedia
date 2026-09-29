-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_332
-- name    : FiniteTriangular.sum_range_332
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:34:06.468041+00:00
-- url     : https://prove2.me/theorems/8d487945-3a74-4eb8-a488-be30e00ae66f
-- title:
--   Sum of integers below 332
-- statement:
--   The sum of the nonnegative integers strictly less than $332$ equals $54946$. Equivalently, $\\sum_{k=0}^{332-1} k = 332(332-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_332 : ∑ k ∈ range 332, k = 54946 := by sorry

end FiniteTriangular
