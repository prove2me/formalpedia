-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1110
-- name    : FiniteTriangular.sum_range_1110
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T17:27:27.618898+00:00
-- url     : https://prove2.me/theorems/db521e60-ef23-46bb-8ee0-5de55530524f
-- title:
--   Sum of the nonnegative integers below 1110
-- statement:
--   The sum of the integers from $0$ through $1109$ equals $615495$, which is the triangular number $\\frac{1110(1109)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1110 : ∑ k ∈ range 1110, k = 615495 := by sorry
end FiniteTriangular
