-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_534
-- name    : FiniteTriangular.sum_range_534
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:27:19.273484+00:00
-- url     : https://prove2.me/theorems/5ac8ee4f-1fe4-4935-be49-1e6e08b338f1
-- title:
--   Sum of integers below 534
-- statement:
--   The sum of the nonnegative integers strictly less than $534$ equals $142311$. Equivalently, $\\sum_{k=0}^{534-1} k = 534(534-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_534 : ∑ k ∈ range 534, k = 142311 := by sorry

end FiniteTriangular
