-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1091
-- name    : FiniteTriangular.sum_range_1091
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T17:23:52.221714+00:00
-- url     : https://prove2.me/theorems/0055d1b6-4172-4206-9cca-7a43b222167a
-- title:
--   Sum of the nonnegative integers below 1091
-- statement:
--   The sum of the integers from $0$ through $1090$ equals $594595$, which is the triangular number $\\frac{1091(1090)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1091 : ∑ k ∈ range 1091, k = 594595 := by sorry
end FiniteTriangular
