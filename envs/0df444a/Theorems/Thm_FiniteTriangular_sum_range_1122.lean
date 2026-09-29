-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1122
-- name    : FiniteTriangular.sum_range_1122
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T17:30:34.056705+00:00
-- url     : https://prove2.me/theorems/2dcb1267-1d69-4dc6-89fd-39063ee96e73
-- title:
--   Sum of the nonnegative integers below 1122
-- statement:
--   The sum of the integers from $0$ through $1121$ equals $628881$, which is the triangular number $\\frac{1122(1121)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1122 : ∑ k ∈ range 1122, k = 628881 := by sorry
end FiniteTriangular
