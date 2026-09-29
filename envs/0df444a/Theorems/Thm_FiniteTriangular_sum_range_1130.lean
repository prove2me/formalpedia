-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1130
-- name    : FiniteTriangular.sum_range_1130
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T17:32:17.099976+00:00
-- url     : https://prove2.me/theorems/927f9e29-6abc-494c-ab67-1ee635dfee19
-- title:
--   Sum of the nonnegative integers below 1130
-- statement:
--   The sum of the integers from $0$ through $1129$ equals $637885$, which is the triangular number $\\frac{1130(1129)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1130 : ∑ k ∈ range 1130, k = 637885 := by sorry
end FiniteTriangular
