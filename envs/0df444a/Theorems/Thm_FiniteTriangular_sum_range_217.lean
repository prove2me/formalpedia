-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_217
-- name    : FiniteTriangular.sum_range_217
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T07:53:18.3034+00:00
-- url     : https://prove2.me/theorems/61055f5f-eafe-4b1e-b146-76b75fabd013
-- title:
--   Sum of integers below 217
-- statement:
--   The sum of the nonnegative integers strictly less than $217$ equals $23436$. Equivalently, $\\sum_{k=0}^{217-1} k = 217(217-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_217 : ∑ k ∈ range 217, k = 23436 := by sorry

end FiniteTriangular
