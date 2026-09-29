-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_716
-- name    : FiniteTriangular.sum_range_716
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:08:40.066011+00:00
-- url     : https://prove2.me/theorems/9ecc6985-6e46-4243-9f0c-5375d6d0ac84
-- title:
--   Sum of integers below 716
-- statement:
--   The sum of the nonnegative integers strictly less than $716$ equals $255970$. Equivalently, $\\sum_{k=0}^{716-1} k = 716(716-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_716 : ∑ k ∈ range 716, k = 255970 := by sorry

end FiniteTriangular
