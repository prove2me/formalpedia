-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_208
-- name    : FiniteTriangular.sum_range_208
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T07:49:17.640401+00:00
-- url     : https://prove2.me/theorems/c8864c66-79f7-468f-833f-478a491a9dd5
-- title:
--   Sum of integers below 208
-- statement:
--   The sum of the nonnegative integers strictly less than $208$ equals $21528$. Equivalently, $\\sum_{k=0}^{208-1} k = 208(208-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_208 : ∑ k ∈ range 208, k = 21528 := by sorry

end FiniteTriangular
