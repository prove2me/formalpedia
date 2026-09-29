-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1016
-- name    : FiniteTriangular.sum_range_1016
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T10:42:18.820405+00:00
-- url     : https://prove2.me/theorems/021eeace-d4fd-4beb-a4ac-5f114a490ea4
-- title:
--   Sum of the nonnegative integers below 1016
-- statement:
--   The sum of the integers from $0$ through $1015$ equals $515620$, which is the triangular number $\\frac{1016(1015)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1016 : ∑ k ∈ range 1016, k = 515620 := by sorry
end FiniteTriangular
