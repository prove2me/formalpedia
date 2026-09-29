-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1081
-- name    : FiniteTriangular.sum_range_1081
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T17:22:18.418377+00:00
-- url     : https://prove2.me/theorems/4e85e874-5c20-4f51-9abb-45025140fe32
-- title:
--   Sum of the nonnegative integers below 1081
-- statement:
--   The sum of the integers from $0$ through $1080$ equals $583740$, which is the triangular number $\\frac{1081(1080)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1081 : ∑ k ∈ range 1081, k = 583740 := by sorry
end FiniteTriangular
