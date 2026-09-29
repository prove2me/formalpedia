-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_941
-- name    : FiniteTriangular.sum_range_941
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:57:00.4685+00:00
-- url     : https://prove2.me/theorems/957cb52e-1609-46a8-8029-c1ffced70b3e
-- title:
--   Sum of integers below 941
-- statement:
--   The sum of the nonnegative integers strictly less than $941$ equals $442270$. Equivalently, $\\sum_{k=0}^{941-1} k = 941(941-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_941 : ∑ k ∈ range 941, k = 442270 := by sorry

end FiniteTriangular
