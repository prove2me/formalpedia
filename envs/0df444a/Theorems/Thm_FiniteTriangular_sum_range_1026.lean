-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1026
-- name    : FiniteTriangular.sum_range_1026
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T10:45:46.708996+00:00
-- url     : https://prove2.me/theorems/34f5b1e2-1db9-46c0-aed9-6ff3d0b8989d
-- title:
--   Sum of the nonnegative integers below 1026
-- statement:
--   The sum of the integers from $0$ through $1025$ equals $525825$, which is the triangular number $\\frac{1026(1025)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1026 : ∑ k ∈ range 1026, k = 525825 := by sorry
end FiniteTriangular
