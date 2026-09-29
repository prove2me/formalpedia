-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1074
-- name    : FiniteTriangular.sum_range_1074
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T17:20:23.875891+00:00
-- url     : https://prove2.me/theorems/ac2c7292-274f-4f40-9c78-7e70ae313ca2
-- title:
--   Sum of the nonnegative integers below 1074
-- statement:
--   The sum of the integers from $0$ through $1073$ equals $576201$, which is the triangular number $\\frac{1074(1073)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1074 : ∑ k ∈ range 1074, k = 576201 := by sorry
end FiniteTriangular
