-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1086
-- name    : FiniteTriangular.sum_range_1086
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T17:22:21.88939+00:00
-- url     : https://prove2.me/theorems/cc7f25e3-0676-4b59-a0b8-62317985061e
-- title:
--   Sum of the nonnegative integers below 1086
-- statement:
--   The sum of the integers from $0$ through $1085$ equals $589155$, which is the triangular number $\\frac{1086(1085)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1086 : ∑ k ∈ range 1086, k = 589155 := by sorry
end FiniteTriangular
