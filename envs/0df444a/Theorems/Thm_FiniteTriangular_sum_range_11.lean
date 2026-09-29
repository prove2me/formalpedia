-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_11
-- name    : FiniteTriangular.sum_range_11
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:03:46.859407+00:00
-- url     : https://prove2.me/theorems/9e5b6e73-434c-4176-9c88-7e58ca860619
-- title:
--   Sum of integers below 11
-- statement:
--   The sum of the nonnegative integers strictly less than $11$ equals $55$. Equivalently, $\sum_{k=0}^{11-1} k = 11(11-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_11 : ∑ k ∈ range 11, k = 55 := by sorry

end FiniteTriangular
