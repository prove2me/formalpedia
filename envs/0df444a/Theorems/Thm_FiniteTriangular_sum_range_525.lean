-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_525
-- name    : FiniteTriangular.sum_range_525
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:25:40.573677+00:00
-- url     : https://prove2.me/theorems/f8ef2366-878a-4d85-9a88-8bce49e15d8f
-- title:
--   Sum of integers below 525
-- statement:
--   The sum of the nonnegative integers strictly less than $525$ equals $137550$. Equivalently, $\\sum_{k=0}^{525-1} k = 525(525-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_525 : ∑ k ∈ range 525, k = 137550 := by sorry

end FiniteTriangular
