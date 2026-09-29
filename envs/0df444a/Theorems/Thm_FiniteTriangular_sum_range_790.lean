-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_790
-- name    : FiniteTriangular.sum_range_790
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:24:54.378758+00:00
-- url     : https://prove2.me/theorems/357fb1b8-f752-4afb-aff0-13dd10ca368d
-- title:
--   Sum of integers below 790
-- statement:
--   The sum of the nonnegative integers strictly less than $790$ equals $311655$. Equivalently, $\\sum_{k=0}^{790-1} k = 790(790-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_790 : ∑ k ∈ range 790, k = 311655 := by sorry

end FiniteTriangular
