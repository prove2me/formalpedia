-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1089
-- name    : FiniteTriangular.sum_range_1089
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T17:23:53.397224+00:00
-- url     : https://prove2.me/theorems/565395aa-18da-4519-a95e-f4432b2841c9
-- title:
--   Sum of the nonnegative integers below 1089
-- statement:
--   The sum of the integers from $0$ through $1088$ equals $592416$, which is the triangular number $\\frac{1089(1088)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1089 : ∑ k ∈ range 1089, k = 592416 := by sorry
end FiniteTriangular
