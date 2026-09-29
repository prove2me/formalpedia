-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_633
-- name    : FiniteTriangular.sum_range_633
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:51:37.551722+00:00
-- url     : https://prove2.me/theorems/17e5317d-6b68-4fd1-aeca-0e80cf93279a
-- title:
--   Sum of integers below 633
-- statement:
--   The sum of the nonnegative integers strictly less than $633$ equals $200028$. Equivalently, $\\sum_{k=0}^{633-1} k = 633(633-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_633 : ∑ k ∈ range 633, k = 200028 := by sorry

end FiniteTriangular
