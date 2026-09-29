-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_624
-- name    : FiniteTriangular.sum_range_624
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:48:08.438138+00:00
-- url     : https://prove2.me/theorems/69ce7082-93d1-4934-8566-691d3a53a676
-- title:
--   Sum of integers below 624
-- statement:
--   The sum of the nonnegative integers strictly less than $624$ equals $194376$. Equivalently, $\\sum_{k=0}^{624-1} k = 624(624-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_624 : ∑ k ∈ range 624, k = 194376 := by sorry

end FiniteTriangular
