-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_412
-- name    : FiniteTriangular.sum_range_412
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T09:52:08.070546+00:00
-- url     : https://prove2.me/theorems/b3ed559b-3702-4a4a-ab73-e5920eb3789a
-- title:
--   Sum of integers below 412
-- statement:
--   The sum of the nonnegative integers strictly less than $412$ equals $84666$. Equivalently, $\\sum_{k=0}^{412-1} k = 412(412-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_412 : ∑ k ∈ range 412, k = 84666 := by sorry

end FiniteTriangular
