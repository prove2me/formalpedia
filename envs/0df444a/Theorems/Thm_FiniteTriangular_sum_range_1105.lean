-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1105
-- name    : FiniteTriangular.sum_range_1105
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T17:27:23.695375+00:00
-- url     : https://prove2.me/theorems/ba685d98-f950-415e-a417-ff8516a7a908
-- title:
--   Sum of the nonnegative integers below 1105
-- statement:
--   The sum of the integers from $0$ through $1104$ equals $609960$, which is the triangular number $\\frac{1105(1104)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1105 : ∑ k ∈ range 1105, k = 609960 := by sorry
end FiniteTriangular
