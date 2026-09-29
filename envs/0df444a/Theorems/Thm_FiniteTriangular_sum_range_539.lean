-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_539
-- name    : FiniteTriangular.sum_range_539
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:28:53.719384+00:00
-- url     : https://prove2.me/theorems/e4cd3190-dd55-4b17-9236-24de82093563
-- title:
--   Sum of integers below 539
-- statement:
--   The sum of the nonnegative integers strictly less than $539$ equals $144991$. Equivalently, $\\sum_{k=0}^{539-1} k = 539(539-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_539 : ∑ k ∈ range 539, k = 144991 := by sorry

end FiniteTriangular
