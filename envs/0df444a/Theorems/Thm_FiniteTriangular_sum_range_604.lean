-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_604
-- name    : FiniteTriangular.sum_range_604
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:44:45.948241+00:00
-- url     : https://prove2.me/theorems/49cec07f-a141-4b22-858c-3d1ac316e462
-- title:
--   Sum of integers below 604
-- statement:
--   The sum of the nonnegative integers strictly less than $604$ equals $182106$. Equivalently, $\\sum_{k=0}^{604-1} k = 604(604-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_604 : ∑ k ∈ range 604, k = 182106 := by sorry

end FiniteTriangular
