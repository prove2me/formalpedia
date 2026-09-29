-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1071
-- name    : FiniteTriangular.sum_range_1071
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T17:18:38.863766+00:00
-- url     : https://prove2.me/theorems/2dd41714-9aba-4e4b-ba82-62814ad6c2dc
-- title:
--   Sum of the nonnegative integers below 1071
-- statement:
--   The sum of the integers from $0$ through $1070$ equals $572985$, which is the triangular number $\\frac{1071(1070)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1071 : ∑ k ∈ range 1071, k = 572985 := by sorry
end FiniteTriangular
