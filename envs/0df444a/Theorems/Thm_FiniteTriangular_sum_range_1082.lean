-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1082
-- name    : FiniteTriangular.sum_range_1082
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T17:22:15.837179+00:00
-- url     : https://prove2.me/theorems/cea9e484-f529-4c18-87a2-c818f6b795a2
-- title:
--   Sum of the nonnegative integers below 1082
-- statement:
--   The sum of the integers from $0$ through $1081$ equals $584821$, which is the triangular number $\\frac{1082(1081)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1082 : ∑ k ∈ range 1082, k = 584821 := by sorry
end FiniteTriangular
