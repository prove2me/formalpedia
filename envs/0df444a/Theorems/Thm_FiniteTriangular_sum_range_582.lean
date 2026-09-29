-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_582
-- name    : FiniteTriangular.sum_range_582
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:39:35.71145+00:00
-- url     : https://prove2.me/theorems/a221fff2-1f39-40ff-96bf-56ddb1ac78d4
-- title:
--   Sum of integers below 582
-- statement:
--   The sum of the nonnegative integers strictly less than $582$ equals $169071$. Equivalently, $\\sum_{k=0}^{582-1} k = 582(582-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_582 : ∑ k ∈ range 582, k = 169071 := by sorry

end FiniteTriangular
