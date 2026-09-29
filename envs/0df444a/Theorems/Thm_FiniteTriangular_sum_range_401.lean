-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_401
-- name    : FiniteTriangular.sum_range_401
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:50:21.555604+00:00
-- url     : https://prove2.me/theorems/eae45f92-ff3e-405e-9e0f-1699e417868b
-- title:
--   Sum of integers below 401
-- statement:
--   The sum of the nonnegative integers strictly less than $401$ equals $80200$. Equivalently, $\\sum_{k=0}^{401-1} k = 401(401-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_401 : ∑ k ∈ range 401, k = 80200 := by sorry

end FiniteTriangular
