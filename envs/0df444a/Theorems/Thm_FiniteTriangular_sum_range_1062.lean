-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1062
-- name    : FiniteTriangular.sum_range_1062
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T17:16:38.274141+00:00
-- url     : https://prove2.me/theorems/f193b310-b7fe-406c-b2ec-92a195cca528
-- title:
--   Sum of the nonnegative integers below 1062
-- statement:
--   The sum of the integers from $0$ through $1061$ equals $563391$, which is the triangular number $\\frac{1062(1061)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1062 : ∑ k ∈ range 1062, k = 563391 := by sorry
end FiniteTriangular
