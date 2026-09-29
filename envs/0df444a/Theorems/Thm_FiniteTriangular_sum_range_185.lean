-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_185
-- name    : FiniteTriangular.sum_range_185
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T07:45:08.328651+00:00
-- url     : https://prove2.me/theorems/3c92ff45-3966-4d77-bf30-5e1b6e392ca8
-- title:
--   Sum of integers below 185
-- statement:
--   The sum of the nonnegative integers strictly less than $185$ equals $17020$. Equivalently, $\\sum_{k=0}^{185-1} k = 185(185-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_185 : ∑ k ∈ range 185, k = 17020 := by sorry

end FiniteTriangular
