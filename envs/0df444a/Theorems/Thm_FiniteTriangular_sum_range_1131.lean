-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1131
-- name    : FiniteTriangular.sum_range_1131
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T17:32:16.962388+00:00
-- url     : https://prove2.me/theorems/366a1b37-b8d0-475f-b2ff-1f84c38d794f
-- title:
--   Sum of the nonnegative integers below 1131
-- statement:
--   The sum of the integers from $0$ through $1130$ equals $639015$, which is the triangular number $\\frac{1131(1130)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1131 : ∑ k ∈ range 1131, k = 639015 := by sorry
end FiniteTriangular
