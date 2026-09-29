-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1009
-- name    : FiniteTriangular.sum_range_1009
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T10:42:22.377983+00:00
-- url     : https://prove2.me/theorems/0b902c04-34b5-4cbc-af5b-14636e3e2646
-- title:
--   Sum of the nonnegative integers below 1009
-- statement:
--   The sum of the integers from $0$ through $1008$ equals $508536$, which is the triangular number $\\frac{1009(1008)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1009 : ∑ k ∈ range 1009, k = 508536 := by sorry
end FiniteTriangular
