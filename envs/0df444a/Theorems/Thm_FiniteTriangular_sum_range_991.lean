-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_991
-- name    : FiniteTriangular.sum_range_991
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T10:36:56.919192+00:00
-- url     : https://prove2.me/theorems/c629d6a8-468d-4ce7-b64f-61ae1354520f
-- title:
--   Sum of the nonnegative integers below 991
-- statement:
--   The sum of the integers from $0$ through $990$ equals $490545$, which is the triangular number $\\frac{991(990)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_991 : ∑ k ∈ range 991, k = 490545 := by sorry
end FiniteTriangular
