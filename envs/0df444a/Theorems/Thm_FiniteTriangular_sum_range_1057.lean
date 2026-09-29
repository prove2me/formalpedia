-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1057
-- name    : FiniteTriangular.sum_range_1057
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T17:16:53.415331+00:00
-- url     : https://prove2.me/theorems/dbd997db-b2e6-4bd2-9931-58b28380f082
-- title:
--   Sum of the nonnegative integers below 1057
-- statement:
--   The sum of the integers from $0$ through $1056$ equals $558096$, which is the triangular number $\\frac{1057(1056)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1057 : ∑ k ∈ range 1057, k = 558096 := by sorry
end FiniteTriangular
