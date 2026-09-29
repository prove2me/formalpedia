-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_996
-- name    : FiniteTriangular.sum_range_996
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T10:38:44.11798+00:00
-- url     : https://prove2.me/theorems/6113b067-4342-43b7-9725-14b7e63e1007
-- title:
--   Sum of the nonnegative integers below 996
-- statement:
--   The sum of the integers from $0$ through $995$ equals $495510$, which is the triangular number $\\frac{996(995)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_996 : ∑ k ∈ range 996, k = 495510 := by sorry
end FiniteTriangular
