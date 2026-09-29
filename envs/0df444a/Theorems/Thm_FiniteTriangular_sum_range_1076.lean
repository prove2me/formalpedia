-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1076
-- name    : FiniteTriangular.sum_range_1076
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T17:20:23.360389+00:00
-- url     : https://prove2.me/theorems/70983d2a-edc6-4f16-8fe9-c6bef1809237
-- title:
--   Sum of the nonnegative integers below 1076
-- statement:
--   The sum of the integers from $0$ through $1075$ equals $578350$, which is the triangular number $\\frac{1076(1075)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1076 : ∑ k ∈ range 1076, k = 578350 := by sorry
end FiniteTriangular
