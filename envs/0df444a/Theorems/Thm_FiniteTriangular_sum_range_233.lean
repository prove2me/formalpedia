-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_233
-- name    : FiniteTriangular.sum_range_233
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T07:57:30.742882+00:00
-- url     : https://prove2.me/theorems/b5190b36-fa1a-4464-95c6-1b3a8f561c30
-- title:
--   Sum of integers below 233
-- statement:
--   The sum of the nonnegative integers strictly less than $233$ equals $27028$. Equivalently, $\\sum_{k=0}^{233-1} k = 233(233-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_233 : ∑ k ∈ range 233, k = 27028 := by sorry

end FiniteTriangular
