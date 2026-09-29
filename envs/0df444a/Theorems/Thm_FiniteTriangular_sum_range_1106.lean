-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1106
-- name    : FiniteTriangular.sum_range_1106
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T17:27:24.552592+00:00
-- url     : https://prove2.me/theorems/737f1bd2-ff04-4f38-8094-90c6904c87d6
-- title:
--   Sum of the nonnegative integers below 1106
-- statement:
--   The sum of the integers from $0$ through $1105$ equals $611065$, which is the triangular number $\\frac{1106(1105)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1106 : ∑ k ∈ range 1106, k = 611065 := by sorry
end FiniteTriangular
