-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_990
-- name    : FiniteTriangular.sum_range_990
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T10:36:52.957279+00:00
-- url     : https://prove2.me/theorems/dd896188-8ee5-42d3-ab40-1d15e68e9ab8
-- title:
--   Sum of the nonnegative integers below 990
-- statement:
--   The sum of the integers from $0$ through $989$ equals $489555$, which is the triangular number $\\frac{990(989)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_990 : ∑ k ∈ range 990, k = 489555 := by sorry
end FiniteTriangular
