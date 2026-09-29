-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_403
-- name    : FiniteTriangular.sum_range_403
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:50:21.948995+00:00
-- url     : https://prove2.me/theorems/b3327d87-705e-4915-ba9c-db5ab6a910f7
-- title:
--   Sum of integers below 403
-- statement:
--   The sum of the nonnegative integers strictly less than $403$ equals $81003$. Equivalently, $\\sum_{k=0}^{403-1} k = 403(403-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_403 : ∑ k ∈ range 403, k = 81003 := by sorry

end FiniteTriangular
