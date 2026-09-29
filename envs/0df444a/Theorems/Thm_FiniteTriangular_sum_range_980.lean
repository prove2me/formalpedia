-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_980
-- name    : FiniteTriangular.sum_range_980
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T10:34:59.609216+00:00
-- url     : https://prove2.me/theorems/a4cdac6f-5cf1-406d-a256-800a48eb096a
-- title:
--   Sum of the nonnegative integers below 980
-- statement:
--   The sum of the integers from $0$ through $979$ equals $479710$, which is the triangular number $\\frac{980(979)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_980 : ∑ k ∈ range 980, k = 479710 := by sorry
end FiniteTriangular
