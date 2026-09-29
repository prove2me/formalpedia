-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_690
-- name    : FiniteTriangular.sum_range_690
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:03:24.518487+00:00
-- url     : https://prove2.me/theorems/8678ca33-15df-4d88-af70-07129ef92a63
-- title:
--   Sum of integers below 690
-- statement:
--   The sum of the nonnegative integers strictly less than $690$ equals $237705$. Equivalently, $\\sum_{k=0}^{690-1} k = 690(690-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_690 : ∑ k ∈ range 690, k = 237705 := by sorry

end FiniteTriangular
