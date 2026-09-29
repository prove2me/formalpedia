-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1019
-- name    : FiniteTriangular.sum_range_1019
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T10:44:00.38798+00:00
-- url     : https://prove2.me/theorems/b4e9b87b-f663-4fb7-a46c-508740e6c6b3
-- title:
--   Sum of the nonnegative integers below 1019
-- statement:
--   The sum of the integers from $0$ through $1018$ equals $518671$, which is the triangular number $\\frac{1019(1018)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1019 : ∑ k ∈ range 1019, k = 518671 := by sorry
end FiniteTriangular
