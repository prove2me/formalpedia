-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1067
-- name    : FiniteTriangular.sum_range_1067
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T17:18:42.799478+00:00
-- url     : https://prove2.me/theorems/38049913-8100-4335-898a-1be8bcd679ff
-- title:
--   Sum of the nonnegative integers below 1067
-- statement:
--   The sum of the integers from $0$ through $1066$ equals $568711$, which is the triangular number $\\frac{1067(1066)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1067 : ∑ k ∈ range 1067, k = 568711 := by sorry
end FiniteTriangular
