-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1099
-- name    : FiniteTriangular.sum_range_1099
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T17:25:35.360233+00:00
-- url     : https://prove2.me/theorems/14848cbc-330b-4a0a-9a0b-617e9dca2f1c
-- title:
--   Sum of the nonnegative integers below 1099
-- statement:
--   The sum of the integers from $0$ through $1098$ equals $603351$, which is the triangular number $\\frac{1099(1098)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1099 : ∑ k ∈ range 1099, k = 603351 := by sorry
end FiniteTriangular
