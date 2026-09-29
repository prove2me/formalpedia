-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1073
-- name    : FiniteTriangular.sum_range_1073
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T17:20:22.305705+00:00
-- url     : https://prove2.me/theorems/9d966d82-f48a-44f0-8a6a-857240f2785f
-- title:
--   Sum of the nonnegative integers below 1073
-- statement:
--   The sum of the integers from $0$ through $1072$ equals $575128$, which is the triangular number $\\frac{1073(1072)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1073 : ∑ k ∈ range 1073, k = 575128 := by sorry
end FiniteTriangular
