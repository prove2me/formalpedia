-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_979
-- name    : FiniteTriangular.sum_range_979
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T10:35:02.589028+00:00
-- url     : https://prove2.me/theorems/78fbf283-8a58-4c17-96fd-66aa63e4158f
-- title:
--   Sum of the nonnegative integers below 979
-- statement:
--   The sum of the integers from $0$ through $978$ equals $478731$, which is the triangular number $\\frac{979(978)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_979 : ∑ k ∈ range 979, k = 478731 := by sorry
end FiniteTriangular
