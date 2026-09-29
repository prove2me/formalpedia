-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_335
-- name    : FiniteTriangular.sum_range_335
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:34:08.38719+00:00
-- url     : https://prove2.me/theorems/59187f78-b55b-481a-aa3c-22789b7fdb90
-- title:
--   Sum of integers below 335
-- statement:
--   The sum of the nonnegative integers strictly less than $335$ equals $55945$. Equivalently, $\\sum_{k=0}^{335-1} k = 335(335-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_335 : ∑ k ∈ range 335, k = 55945 := by sorry

end FiniteTriangular
