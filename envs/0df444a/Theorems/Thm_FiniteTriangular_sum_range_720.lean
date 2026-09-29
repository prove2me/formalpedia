-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_720
-- name    : FiniteTriangular.sum_range_720
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:08:41.355423+00:00
-- url     : https://prove2.me/theorems/114db995-b508-41ca-95fa-603c3c2c2316
-- title:
--   Sum of integers below 720
-- statement:
--   The sum of the nonnegative integers strictly less than $720$ equals $258840$. Equivalently, $\\sum_{k=0}^{720-1} k = 720(720-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_720 : ∑ k ∈ range 720, k = 258840 := by sorry

end FiniteTriangular
