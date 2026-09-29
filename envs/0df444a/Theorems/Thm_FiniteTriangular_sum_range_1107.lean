-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1107
-- name    : FiniteTriangular.sum_range_1107
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T17:27:24.696342+00:00
-- url     : https://prove2.me/theorems/55ed4fde-a502-4c7f-9ebc-03e693a3488a
-- title:
--   Sum of the nonnegative integers below 1107
-- statement:
--   The sum of the integers from $0$ through $1106$ equals $612171$, which is the triangular number $\\frac{1107(1106)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1107 : ∑ k ∈ range 1107, k = 612171 := by sorry
end FiniteTriangular
