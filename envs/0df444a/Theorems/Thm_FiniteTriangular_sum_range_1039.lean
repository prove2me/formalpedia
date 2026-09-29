-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1039
-- name    : FiniteTriangular.sum_range_1039
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T10:47:49.562975+00:00
-- url     : https://prove2.me/theorems/d93d9927-2dcb-47ef-a0f7-97557f7db3a5
-- title:
--   Sum of the nonnegative integers below 1039
-- statement:
--   The sum of the integers from $0$ through $1038$ equals $539241$, which is the triangular number $\\frac{1039(1038)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1039 : ∑ k ∈ range 1039, k = 539241 := by sorry
end FiniteTriangular
