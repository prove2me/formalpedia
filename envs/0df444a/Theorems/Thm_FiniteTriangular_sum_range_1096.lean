-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1096
-- name    : FiniteTriangular.sum_range_1096
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T17:23:55.375765+00:00
-- url     : https://prove2.me/theorems/1a992370-9bf6-45d9-a06f-6e31a87d9b6e
-- title:
--   Sum of the nonnegative integers below 1096
-- statement:
--   The sum of the integers from $0$ through $1095$ equals $600060$, which is the triangular number $\\frac{1096(1095)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1096 : ∑ k ∈ range 1096, k = 600060 := by sorry
end FiniteTriangular
