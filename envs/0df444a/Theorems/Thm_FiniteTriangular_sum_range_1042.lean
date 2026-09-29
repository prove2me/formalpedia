-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1042
-- name    : FiniteTriangular.sum_range_1042
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T17:13:11.436515+00:00
-- url     : https://prove2.me/theorems/17dd71b3-0715-464c-84dc-f8982ac6f0c6
-- title:
--   Sum of the nonnegative integers below 1042
-- statement:
--   The sum of the integers from $0$ through $1041$ equals $542361$, which is the triangular number $\\frac{1042(1041)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1042 : ∑ k ∈ range 1042, k = 542361 := by sorry
end FiniteTriangular
