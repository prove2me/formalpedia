-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_399
-- name    : FiniteTriangular.sum_range_399
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:48:43.83983+00:00
-- url     : https://prove2.me/theorems/330bbfbf-b964-471c-a49f-93cb77de458a
-- title:
--   Sum of integers below 399
-- statement:
--   The sum of the nonnegative integers strictly less than $399$ equals $79401$. Equivalently, $\\sum_{k=0}^{399-1} k = 399(399-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_399 : ∑ k ∈ range 399, k = 79401 := by sorry

end FiniteTriangular
