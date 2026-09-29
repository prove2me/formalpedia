-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1090
-- name    : FiniteTriangular.sum_range_1090
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T17:23:52.044441+00:00
-- url     : https://prove2.me/theorems/86a3bcc9-1e14-4d9e-8d98-c4845c85c273
-- title:
--   Sum of the nonnegative integers below 1090
-- statement:
--   The sum of the integers from $0$ through $1089$ equals $593505$, which is the triangular number $\\frac{1090(1089)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1090 : ∑ k ∈ range 1090, k = 593505 := by sorry
end FiniteTriangular
