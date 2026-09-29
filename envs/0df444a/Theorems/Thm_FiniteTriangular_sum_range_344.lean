-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_344
-- name    : FiniteTriangular.sum_range_344
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:35:52.470674+00:00
-- url     : https://prove2.me/theorems/371f5f55-b623-4774-881d-b99e28e953a0
-- title:
--   Sum of integers below 344
-- statement:
--   The sum of the nonnegative integers strictly less than $344$ equals $58996$. Equivalently, $\\sum_{k=0}^{344-1} k = 344(344-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_344 : ∑ k ∈ range 344, k = 58996 := by sorry

end FiniteTriangular
