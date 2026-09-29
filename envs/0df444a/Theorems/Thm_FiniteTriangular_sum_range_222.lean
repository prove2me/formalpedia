-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_222
-- name    : FiniteTriangular.sum_range_222
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T07:53:18.981745+00:00
-- url     : https://prove2.me/theorems/c83fe299-f684-4d7d-b1cf-ecd76ef1daab
-- title:
--   Sum of integers below 222
-- statement:
--   The sum of the nonnegative integers strictly less than $222$ equals $24531$. Equivalently, $\\sum_{k=0}^{222-1} k = 222(222-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_222 : ∑ k ∈ range 222, k = 24531 := by sorry

end FiniteTriangular
