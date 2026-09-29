-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_981
-- name    : FiniteTriangular.sum_range_981
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T10:35:00.565974+00:00
-- url     : https://prove2.me/theorems/dc99925f-78b0-40c1-be91-36ec599b9712
-- title:
--   Sum of the nonnegative integers below 981
-- statement:
--   The sum of the integers from $0$ through $980$ equals $480690$, which is the triangular number $\\frac{981(980)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_981 : ∑ k ∈ range 981, k = 480690 := by sorry
end FiniteTriangular
