-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1020
-- name    : FiniteTriangular.sum_range_1020
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T10:44:03.080993+00:00
-- url     : https://prove2.me/theorems/7ccb2f61-6a38-482a-b750-9f6eac4ec91d
-- title:
--   Sum of the nonnegative integers below 1020
-- statement:
--   The sum of the integers from $0$ through $1019$ equals $519690$, which is the triangular number $\\frac{1020(1019)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1020 : ∑ k ∈ range 1020, k = 519690 := by sorry
end FiniteTriangular
