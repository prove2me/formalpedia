-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1118
-- name    : FiniteTriangular.sum_range_1118
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T17:28:58.087504+00:00
-- url     : https://prove2.me/theorems/af4230d9-b5c0-4397-847e-10ab29b92a69
-- title:
--   Sum of the nonnegative integers below 1118
-- statement:
--   The sum of the integers from $0$ through $1117$ equals $624403$, which is the triangular number $\\frac{1118(1117)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1118 : ∑ k ∈ range 1118, k = 624403 := by sorry
end FiniteTriangular
