-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_370
-- name    : FiniteTriangular.sum_range_370
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:43:06.91604+00:00
-- url     : https://prove2.me/theorems/aba38ede-350e-414a-acad-cd6cf4bef853
-- title:
--   Sum of integers below 370
-- statement:
--   The sum of the nonnegative integers strictly less than $370$ equals $68265$. Equivalently, $\\sum_{k=0}^{370-1} k = 370(370-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_370 : ∑ k ∈ range 370, k = 68265 := by sorry

end FiniteTriangular
