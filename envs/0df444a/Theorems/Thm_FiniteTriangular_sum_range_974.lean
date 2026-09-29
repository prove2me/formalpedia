-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_974
-- name    : FiniteTriangular.sum_range_974
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T12:04:17.293671+00:00
-- url     : https://prove2.me/theorems/381f3c84-aac6-4cb3-9ecd-88ecf8ca8825
-- title:
--   Sum of integers below 974
-- statement:
--   The sum of the nonnegative integers strictly less than $974$ equals $473851$. Equivalently, $\\sum_{k=0}^{974-1} k = 974(974-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_974 : ∑ k ∈ range 974, k = 473851 := by sorry

end FiniteTriangular
