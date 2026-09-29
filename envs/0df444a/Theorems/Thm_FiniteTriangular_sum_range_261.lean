-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_261
-- name    : FiniteTriangular.sum_range_261
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T08:11:01.970607+00:00
-- url     : https://prove2.me/theorems/4b24cc1f-1165-437d-99ea-1e10dc9a172b
-- title:
--   Sum of integers below 261
-- statement:
--   The sum of the nonnegative integers strictly less than $261$ equals $33930$. Equivalently, $\\sum_{k=0}^{261-1} k = 261(261-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_261 : ∑ k ∈ range 261, k = 33930 := by sorry

end FiniteTriangular
