-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_455
-- name    : FiniteTriangular.sum_range_455
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:09:51.419356+00:00
-- url     : https://prove2.me/theorems/ec755020-bd8d-46f2-b3bd-175556da7d5d
-- title:
--   Sum of integers below 455
-- statement:
--   The sum of the nonnegative integers strictly less than $455$ equals $103285$. Equivalently, $\\sum_{k=0}^{455-1} k = 455(455-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_455 : ∑ k ∈ range 455, k = 103285 := by sorry

end FiniteTriangular
