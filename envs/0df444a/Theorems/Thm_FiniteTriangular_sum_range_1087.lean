-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1087
-- name    : FiniteTriangular.sum_range_1087
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T17:22:19.928544+00:00
-- url     : https://prove2.me/theorems/95781ae6-94ea-400f-84ed-89b6e17f557f
-- title:
--   Sum of the nonnegative integers below 1087
-- statement:
--   The sum of the integers from $0$ through $1086$ equals $590241$, which is the triangular number $\\frac{1087(1086)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1087 : ∑ k ∈ range 1087, k = 590241 := by sorry
end FiniteTriangular
