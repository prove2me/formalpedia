-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_337
-- name    : FiniteTriangular.sum_range_337
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:35:51.287451+00:00
-- url     : https://prove2.me/theorems/a0e2c86b-67d6-4057-85dd-e74d85b2c802
-- title:
--   Sum of integers below 337
-- statement:
--   The sum of the nonnegative integers strictly less than $337$ equals $56616$. Equivalently, $\\sum_{k=0}^{337-1} k = 337(337-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_337 : ∑ k ∈ range 337, k = 56616 := by sorry

end FiniteTriangular
