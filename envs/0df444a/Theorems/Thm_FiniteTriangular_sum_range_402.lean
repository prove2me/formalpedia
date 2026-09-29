-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_402
-- name    : FiniteTriangular.sum_range_402
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:50:22.65432+00:00
-- url     : https://prove2.me/theorems/a418b241-4f88-4699-8e6f-bfd2f69bcf3a
-- title:
--   Sum of integers below 402
-- statement:
--   The sum of the nonnegative integers strictly less than $402$ equals $80601$. Equivalently, $\\sum_{k=0}^{402-1} k = 402(402-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_402 : ∑ k ∈ range 402, k = 80601 := by sorry

end FiniteTriangular
