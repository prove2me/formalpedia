-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_507
-- name    : FiniteTriangular.sum_range_507
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:22:09.361346+00:00
-- url     : https://prove2.me/theorems/85f53a70-4184-4424-b7f5-669e2e02abb2
-- title:
--   Sum of integers below 507
-- statement:
--   The sum of the nonnegative integers strictly less than $507$ equals $128271$. Equivalently, $\\sum_{k=0}^{507-1} k = 507(507-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_507 : ∑ k ∈ range 507, k = 128271 := by sorry

end FiniteTriangular
