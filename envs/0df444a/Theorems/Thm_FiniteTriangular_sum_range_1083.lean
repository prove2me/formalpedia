-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1083
-- name    : FiniteTriangular.sum_range_1083
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T17:22:15.467071+00:00
-- url     : https://prove2.me/theorems/33015eea-9c8b-4f27-957c-1e6831579533
-- title:
--   Sum of the nonnegative integers below 1083
-- statement:
--   The sum of the integers from $0$ through $1082$ equals $585903$, which is the triangular number $\\frac{1083(1082)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1083 : ∑ k ∈ range 1083, k = 585903 := by sorry
end FiniteTriangular
