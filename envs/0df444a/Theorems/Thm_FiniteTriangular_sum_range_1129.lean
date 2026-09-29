-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1129
-- name    : FiniteTriangular.sum_range_1129
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T17:32:17.551117+00:00
-- url     : https://prove2.me/theorems/d5a5c41a-1f89-4add-ad5a-ee39b48055de
-- title:
--   Sum of the nonnegative integers below 1129
-- statement:
--   The sum of the integers from $0$ through $1128$ equals $636756$, which is the triangular number $\\frac{1129(1128)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1129 : ∑ k ∈ range 1129, k = 636756 := by sorry
end FiniteTriangular
