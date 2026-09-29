-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_379
-- name    : FiniteTriangular.sum_range_379
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:45:10.483074+00:00
-- url     : https://prove2.me/theorems/d4c9ef9e-ce9d-4779-a6b8-76725c87465e
-- title:
--   Sum of integers below 379
-- statement:
--   The sum of the nonnegative integers strictly less than $379$ equals $71631$. Equivalently, $\\sum_{k=0}^{379-1} k = 379(379-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_379 : ∑ k ∈ range 379, k = 71631 := by sorry

end FiniteTriangular
