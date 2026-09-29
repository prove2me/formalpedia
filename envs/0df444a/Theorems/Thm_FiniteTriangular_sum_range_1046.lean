-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1046
-- name    : FiniteTriangular.sum_range_1046
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T17:13:10.833397+00:00
-- url     : https://prove2.me/theorems/c62e6746-1263-41a0-90de-209c42d24a18
-- title:
--   Sum of the nonnegative integers below 1046
-- statement:
--   The sum of the integers from $0$ through $1045$ equals $546535$, which is the triangular number $\\frac{1046(1045)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1046 : ∑ k ∈ range 1046, k = 546535 := by sorry
end FiniteTriangular
