-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_639
-- name    : FiniteTriangular.sum_range_639
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:51:38.096976+00:00
-- url     : https://prove2.me/theorems/650da6a1-09a0-4a36-af53-f1bb3f1a1411
-- title:
--   Sum of integers below 639
-- statement:
--   The sum of the nonnegative integers strictly less than $639$ equals $203841$. Equivalently, $\\sum_{k=0}^{639-1} k = 639(639-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_639 : ∑ k ∈ range 639, k = 203841 := by sorry

end FiniteTriangular
