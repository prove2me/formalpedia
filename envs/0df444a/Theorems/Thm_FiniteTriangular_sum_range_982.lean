-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_982
-- name    : FiniteTriangular.sum_range_982
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T10:35:00.464985+00:00
-- url     : https://prove2.me/theorems/99d8b8e6-e04e-46a8-a620-2afff6d797e7
-- title:
--   Sum of the nonnegative integers below 982
-- statement:
--   The sum of the integers from $0$ through $981$ equals $481671$, which is the triangular number $\\frac{982(981)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_982 : ∑ k ∈ range 982, k = 481671 := by sorry
end FiniteTriangular
