-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_384
-- name    : FiniteTriangular.sum_range_384
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:45:15.549776+00:00
-- url     : https://prove2.me/theorems/410e7e70-aacc-4921-be7e-f8396ac065b3
-- title:
--   Sum of integers below 384
-- statement:
--   The sum of the nonnegative integers strictly less than $384$ equals $73536$. Equivalently, $\\sum_{k=0}^{384-1} k = 384(384-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_384 : ∑ k ∈ range 384, k = 73536 := by sorry

end FiniteTriangular
