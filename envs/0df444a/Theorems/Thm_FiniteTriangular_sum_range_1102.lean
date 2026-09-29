-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1102
-- name    : FiniteTriangular.sum_range_1102
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T17:25:35.62584+00:00
-- url     : https://prove2.me/theorems/56528f6e-0f29-4efc-aa31-e1de55a5ee93
-- title:
--   Sum of the nonnegative integers below 1102
-- statement:
--   The sum of the integers from $0$ through $1101$ equals $606651$, which is the triangular number $\\frac{1102(1101)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1102 : ∑ k ∈ range 1102, k = 606651 := by sorry
end FiniteTriangular
