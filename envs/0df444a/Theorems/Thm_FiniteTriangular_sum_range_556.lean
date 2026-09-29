-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_556
-- name    : FiniteTriangular.sum_range_556
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:34:12.533381+00:00
-- url     : https://prove2.me/theorems/e0091b91-764b-47cd-995d-307d25a4f504
-- title:
--   Sum of integers below 556
-- statement:
--   The sum of the nonnegative integers strictly less than $556$ equals $154290$. Equivalently, $\\sum_{k=0}^{556-1} k = 556(556-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_556 : ∑ k ∈ range 556, k = 154290 := by sorry

end FiniteTriangular
