-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_424
-- name    : FiniteTriangular.sum_range_424
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:53:53.120918+00:00
-- url     : https://prove2.me/theorems/d0bc2a76-57d6-412c-af4d-99d51dbe367b
-- title:
--   Sum of integers below 424
-- statement:
--   The sum of the nonnegative integers strictly less than $424$ equals $89676$. Equivalently, $\\sum_{k=0}^{424-1} k = 424(424-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_424 : ∑ k ∈ range 424, k = 89676 := by sorry

end FiniteTriangular
