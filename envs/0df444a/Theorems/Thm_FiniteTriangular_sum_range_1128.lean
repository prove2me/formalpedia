-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1128
-- name    : FiniteTriangular.sum_range_1128
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T17:30:36.362197+00:00
-- url     : https://prove2.me/theorems/80380f4a-6ae9-42e6-aa07-3f1dcc2d0d85
-- title:
--   Sum of the nonnegative integers below 1128
-- statement:
--   The sum of the integers from $0$ through $1127$ equals $635628$, which is the triangular number $\\frac{1128(1127)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1128 : ∑ k ∈ range 1128, k = 635628 := by sorry
end FiniteTriangular
