-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1001
-- name    : FiniteTriangular.sum_range_1001
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T10:40:41.471986+00:00
-- url     : https://prove2.me/theorems/54e87790-651d-482b-870c-274eb0405733
-- title:
--   Sum of the nonnegative integers below 1001
-- statement:
--   The sum of the integers from $0$ through $1000$ equals $500500$, which is the triangular number $\\frac{1001(1000)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1001 : ∑ k ∈ range 1001, k = 500500 := by sorry
end FiniteTriangular
