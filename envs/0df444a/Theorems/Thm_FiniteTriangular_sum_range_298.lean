-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_298
-- name    : FiniteTriangular.sum_range_298
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T08:19:53.508418+00:00
-- url     : https://prove2.me/theorems/59afcd23-39da-48d3-8e18-961edb3bcf47
-- title:
--   Sum of integers below 298
-- statement:
--   The sum of the nonnegative integers strictly less than $298$ equals $44253$. Equivalently, $\\sum_{k=0}^{298-1} k = 298(298-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_298 : ∑ k ∈ range 298, k = 44253 := by sorry

end FiniteTriangular
