-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1092
-- name    : FiniteTriangular.sum_range_1092
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T17:23:52.596236+00:00
-- url     : https://prove2.me/theorems/de537dad-c116-49f5-b18d-d49e336644eb
-- title:
--   Sum of the nonnegative integers below 1092
-- statement:
--   The sum of the integers from $0$ through $1091$ equals $595686$, which is the triangular number $\\frac{1092(1091)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1092 : ∑ k ∈ range 1092, k = 595686 := by sorry
end FiniteTriangular
