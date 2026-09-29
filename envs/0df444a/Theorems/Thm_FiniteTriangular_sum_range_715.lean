-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_715
-- name    : FiniteTriangular.sum_range_715
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:08:42.178324+00:00
-- url     : https://prove2.me/theorems/3651d9a8-3395-4880-acfc-91c9e5908b4e
-- title:
--   Sum of integers below 715
-- statement:
--   The sum of the nonnegative integers strictly less than $715$ equals $255255$. Equivalently, $\\sum_{k=0}^{715-1} k = 715(715-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_715 : ∑ k ∈ range 715, k = 255255 := by sorry

end FiniteTriangular
