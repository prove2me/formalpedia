-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1056
-- name    : FiniteTriangular.sum_range_1056
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T17:14:55.281098+00:00
-- url     : https://prove2.me/theorems/2eedcbd7-bd26-4745-a162-f422038ecb09
-- title:
--   Sum of the nonnegative integers below 1056
-- statement:
--   The sum of the integers from $0$ through $1055$ equals $557040$, which is the triangular number $\\frac{1056(1055)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1056 : ∑ k ∈ range 1056, k = 557040 := by sorry
end FiniteTriangular
