-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_964
-- name    : FiniteTriangular.sum_range_964
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T12:02:36.775375+00:00
-- url     : https://prove2.me/theorems/be47ae96-be40-4a53-816d-171adedfc81f
-- title:
--   Sum of integers below 964
-- statement:
--   The sum of the nonnegative integers strictly less than $964$ equals $464166$. Equivalently, $\\sum_{k=0}^{964-1} k = 964(964-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_964 : ∑ k ∈ range 964, k = 464166 := by sorry

end FiniteTriangular
