-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_373
-- name    : FiniteTriangular.sum_range_373
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:43:06.921378+00:00
-- url     : https://prove2.me/theorems/ede8c1f7-5e87-4538-b12c-2270ad833d9f
-- title:
--   Sum of integers below 373
-- statement:
--   The sum of the nonnegative integers strictly less than $373$ equals $69378$. Equivalently, $\\sum_{k=0}^{373-1} k = 373(373-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_373 : ∑ k ∈ range 373, k = 69378 := by sorry

end FiniteTriangular
