-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_864
-- name    : FiniteTriangular.sum_range_864
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:39:59.591131+00:00
-- url     : https://prove2.me/theorems/0f260c43-aa4a-4774-b2b0-77e082d3d510
-- title:
--   Sum of integers below 864
-- statement:
--   The sum of the nonnegative integers strictly less than $864$ equals $372816$. Equivalently, $\\sum_{k=0}^{864-1} k = 864(864-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_864 : ∑ k ∈ range 864, k = 372816 := by sorry

end FiniteTriangular
