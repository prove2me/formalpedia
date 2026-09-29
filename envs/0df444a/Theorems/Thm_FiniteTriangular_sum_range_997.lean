-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_997
-- name    : FiniteTriangular.sum_range_997
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T10:38:37.222992+00:00
-- url     : https://prove2.me/theorems/d6ed5563-aded-4a17-90e7-7ccfe1b7a5e8
-- title:
--   Sum of the nonnegative integers below 997
-- statement:
--   The sum of the integers from $0$ through $996$ equals $496506$, which is the triangular number $\\frac{997(996)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_997 : ∑ k ∈ range 997, k = 496506 := by sorry
end FiniteTriangular
