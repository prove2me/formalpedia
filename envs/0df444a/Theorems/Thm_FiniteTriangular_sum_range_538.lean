-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_538
-- name    : FiniteTriangular.sum_range_538
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:28:53.581737+00:00
-- url     : https://prove2.me/theorems/54c80a57-72a7-42af-a7d1-096b44e39f49
-- title:
--   Sum of integers below 538
-- statement:
--   The sum of the nonnegative integers strictly less than $538$ equals $144453$. Equivalently, $\\sum_{k=0}^{538-1} k = 538(538-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_538 : ∑ k ∈ range 538, k = 144453 := by sorry

end FiniteTriangular
