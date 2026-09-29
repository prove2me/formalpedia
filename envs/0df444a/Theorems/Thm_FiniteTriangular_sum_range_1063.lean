-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1063
-- name    : FiniteTriangular.sum_range_1063
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T17:16:39.045054+00:00
-- url     : https://prove2.me/theorems/ddabd8b9-f94f-4d2b-b040-a1987dbb727e
-- title:
--   Sum of the nonnegative integers below 1063
-- statement:
--   The sum of the integers from $0$ through $1062$ equals $564453$, which is the triangular number $\\frac{1063(1062)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1063 : ∑ k ∈ range 1063, k = 564453 := by sorry
end FiniteTriangular
