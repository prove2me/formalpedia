-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_392
-- name    : FiniteTriangular.sum_range_392
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:47:02.3953+00:00
-- url     : https://prove2.me/theorems/0ac898eb-daff-4248-bbca-f3afd536a9c9
-- title:
--   Sum of integers below 392
-- statement:
--   The sum of the nonnegative integers strictly less than $392$ equals $76636$. Equivalently, $\\sum_{k=0}^{392-1} k = 392(392-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_392 : ∑ k ∈ range 392, k = 76636 := by sorry

end FiniteTriangular
