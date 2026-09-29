-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_327
-- name    : FiniteTriangular.sum_range_327
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:32:11.16227+00:00
-- url     : https://prove2.me/theorems/61bc1a3e-7d74-461f-a1ef-3ef3af6e2e78
-- title:
--   Sum of integers below 327
-- statement:
--   The sum of the nonnegative integers strictly less than $327$ equals $53301$. Equivalently, $\\sum_{k=0}^{327-1} k = 327(327-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_327 : ∑ k ∈ range 327, k = 53301 := by sorry

end FiniteTriangular
