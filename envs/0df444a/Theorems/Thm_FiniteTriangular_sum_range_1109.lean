-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1109
-- name    : FiniteTriangular.sum_range_1109
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T17:27:26.004021+00:00
-- url     : https://prove2.me/theorems/d493387e-d5c2-497e-b618-187e8867ef50
-- title:
--   Sum of the nonnegative integers below 1109
-- statement:
--   The sum of the integers from $0$ through $1108$ equals $614386$, which is the triangular number $\\frac{1109(1108)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1109 : ∑ k ∈ range 1109, k = 614386 := by sorry
end FiniteTriangular
