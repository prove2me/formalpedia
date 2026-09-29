-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1033
-- name    : FiniteTriangular.sum_range_1033
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T10:47:38.463985+00:00
-- url     : https://prove2.me/theorems/7fbbcf44-222d-4cfd-9a0c-5a8966d2c032
-- title:
--   Sum of the nonnegative integers below 1033
-- statement:
--   The sum of the integers from $0$ through $1032$ equals $533028$, which is the triangular number $\\frac{1033(1032)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1033 : ∑ k ∈ range 1033, k = 533028 := by sorry
end FiniteTriangular
