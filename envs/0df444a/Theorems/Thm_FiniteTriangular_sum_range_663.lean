-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_663
-- name    : FiniteTriangular.sum_range_663
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:56:36.60382+00:00
-- url     : https://prove2.me/theorems/a7b43b7d-b84b-4575-8617-59a7d16a3bee
-- title:
--   Sum of integers below 663
-- statement:
--   The sum of the nonnegative integers strictly less than $663$ equals $219453$. Equivalently, $\\sum_{k=0}^{663-1} k = 663(663-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_663 : ∑ k ∈ range 663, k = 219453 := by sorry

end FiniteTriangular
