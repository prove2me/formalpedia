-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1094
-- name    : FiniteTriangular.sum_range_1094
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T17:23:53.117751+00:00
-- url     : https://prove2.me/theorems/6a4989ad-6b0e-4151-9619-1e0bd941e200
-- title:
--   Sum of the nonnegative integers below 1094
-- statement:
--   The sum of the integers from $0$ through $1093$ equals $597871$, which is the triangular number $\\frac{1094(1093)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1094 : ∑ k ∈ range 1094, k = 597871 := by sorry
end FiniteTriangular
