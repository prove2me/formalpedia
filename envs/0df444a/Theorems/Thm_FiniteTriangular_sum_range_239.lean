-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_239
-- name    : FiniteTriangular.sum_range_239
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T07:57:33.418602+00:00
-- url     : https://prove2.me/theorems/1619c018-9a5f-4a6e-99f6-bd2a46f4d762
-- title:
--   Sum of integers below 239
-- statement:
--   The sum of the nonnegative integers strictly less than $239$ equals $28441$. Equivalently, $\\sum_{k=0}^{239-1} k = 239(239-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_239 : ∑ k ∈ range 239, k = 28441 := by sorry

end FiniteTriangular
