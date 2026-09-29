-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1030
-- name    : FiniteTriangular.sum_range_1030
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T10:45:44.670472+00:00
-- url     : https://prove2.me/theorems/4f233286-af0e-4a3c-80e4-50b517b0c62a
-- title:
--   Sum of the nonnegative integers below 1030
-- statement:
--   The sum of the integers from $0$ through $1029$ equals $529935$, which is the triangular number $\\frac{1030(1029)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1030 : ∑ k ∈ range 1030, k = 529935 := by sorry
end FiniteTriangular
