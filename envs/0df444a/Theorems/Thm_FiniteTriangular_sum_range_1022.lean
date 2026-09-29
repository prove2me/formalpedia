-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1022
-- name    : FiniteTriangular.sum_range_1022
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T10:44:04.827986+00:00
-- url     : https://prove2.me/theorems/e750cf06-f17c-445f-ad5c-598d81b49d0d
-- title:
--   Sum of the nonnegative integers below 1022
-- statement:
--   The sum of the integers from $0$ through $1021$ equals $521731$, which is the triangular number $\\frac{1022(1021)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1022 : ∑ k ∈ range 1022, k = 521731 := by sorry
end FiniteTriangular
