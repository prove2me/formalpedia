-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_967
-- name    : FiniteTriangular.sum_range_967
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T12:02:33.548339+00:00
-- url     : https://prove2.me/theorems/e9f34367-0244-4b42-8f1e-46dfbe18847f
-- title:
--   Sum of integers below 967
-- statement:
--   The sum of the nonnegative integers strictly less than $967$ equals $467061$. Equivalently, $\\sum_{k=0}^{967-1} k = 967(967-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_967 : ∑ k ∈ range 967, k = 467061 := by sorry

end FiniteTriangular
