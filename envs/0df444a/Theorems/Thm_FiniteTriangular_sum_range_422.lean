-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_422
-- name    : FiniteTriangular.sum_range_422
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:53:52.479676+00:00
-- url     : https://prove2.me/theorems/f798cfd0-47a4-4241-9c1b-ff45663f9350
-- title:
--   Sum of integers below 422
-- statement:
--   The sum of the nonnegative integers strictly less than $422$ equals $88831$. Equivalently, $\\sum_{k=0}^{422-1} k = 422(422-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_422 : ∑ k ∈ range 422, k = 88831 := by sorry

end FiniteTriangular
