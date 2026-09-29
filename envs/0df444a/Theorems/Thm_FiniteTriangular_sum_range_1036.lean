-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1036
-- name    : FiniteTriangular.sum_range_1036
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T10:47:39.062983+00:00
-- url     : https://prove2.me/theorems/35414546-1613-4335-9740-40ecaecabd73
-- title:
--   Sum of the nonnegative integers below 1036
-- statement:
--   The sum of the integers from $0$ through $1035$ equals $536130$, which is the triangular number $\\frac{1036(1035)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1036 : ∑ k ∈ range 1036, k = 536130 := by sorry
end FiniteTriangular
