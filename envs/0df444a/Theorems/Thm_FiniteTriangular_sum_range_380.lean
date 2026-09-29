-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_380
-- name    : FiniteTriangular.sum_range_380
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:45:14.389238+00:00
-- url     : https://prove2.me/theorems/8087bc1c-ffa5-452d-8cc3-74a19a0fb950
-- title:
--   Sum of integers below 380
-- statement:
--   The sum of the nonnegative integers strictly less than $380$ equals $72010$. Equivalently, $\\sum_{k=0}^{380-1} k = 380(380-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_380 : ∑ k ∈ range 380, k = 72010 := by sorry

end FiniteTriangular
