-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_429
-- name    : FiniteTriangular.sum_range_429
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:55:40.361994+00:00
-- url     : https://prove2.me/theorems/e2c5da61-fe58-4790-8148-06d7d1d9be39
-- title:
--   Sum of integers below 429
-- statement:
--   The sum of the nonnegative integers strictly less than $429$ equals $91806$. Equivalently, $\\sum_{k=0}^{429-1} k = 429(429-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_429 : ∑ k ∈ range 429, k = 91806 := by sorry

end FiniteTriangular
