-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_814
-- name    : FiniteTriangular.sum_range_814
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:29:53.685802+00:00
-- url     : https://prove2.me/theorems/20fcfe4b-a2b1-41d6-b4b3-90013b224a9e
-- title:
--   Sum of integers below 814
-- statement:
--   The sum of the nonnegative integers strictly less than $814$ equals $330891$. Equivalently, $\\sum_{k=0}^{814-1} k = 814(814-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_814 : ∑ k ∈ range 814, k = 330891 := by sorry

end FiniteTriangular
