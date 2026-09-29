-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_282
-- name    : FiniteTriangular.sum_range_282
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T08:16:31.676758+00:00
-- url     : https://prove2.me/theorems/90afe38e-f295-40eb-8a16-56d5a7828f05
-- title:
--   Sum of integers below 282
-- statement:
--   The sum of the nonnegative integers strictly less than $282$ equals $39621$. Equivalently, $\\sum_{k=0}^{282-1} k = 282(282-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_282 : ∑ k ∈ range 282, k = 39621 := by sorry

end FiniteTriangular
