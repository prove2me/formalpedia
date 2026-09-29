-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1013
-- name    : FiniteTriangular.sum_range_1013
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T10:42:16.478988+00:00
-- url     : https://prove2.me/theorems/f8e250c3-a008-433a-a2d0-9b54248daf2c
-- title:
--   Sum of the nonnegative integers below 1013
-- statement:
--   The sum of the integers from $0$ through $1012$ equals $512578$, which is the triangular number $\\frac{1013(1012)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1013 : ∑ k ∈ range 1013, k = 512578 := by sorry
end FiniteTriangular
