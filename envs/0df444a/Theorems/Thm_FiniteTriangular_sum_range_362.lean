-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_362
-- name    : FiniteTriangular.sum_range_362
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:41:10.741395+00:00
-- url     : https://prove2.me/theorems/25424379-2636-408d-b83f-4da46cedfb7d
-- title:
--   Sum of integers below 362
-- statement:
--   The sum of the nonnegative integers strictly less than $362$ equals $65341$. Equivalently, $\\sum_{k=0}^{362-1} k = 362(362-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_362 : ∑ k ∈ range 362, k = 65341 := by sorry

end FiniteTriangular
