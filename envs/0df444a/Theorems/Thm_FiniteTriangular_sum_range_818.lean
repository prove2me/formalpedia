-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_818
-- name    : FiniteTriangular.sum_range_818
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:31:45.781625+00:00
-- url     : https://prove2.me/theorems/3d992888-d675-457b-ab58-33a7f3534c7b
-- title:
--   Sum of integers below 818
-- statement:
--   The sum of the nonnegative integers strictly less than $818$ equals $334153$. Equivalently, $\\sum_{k=0}^{818-1} k = 818(818-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_818 : ∑ k ∈ range 818, k = 334153 := by sorry

end FiniteTriangular
