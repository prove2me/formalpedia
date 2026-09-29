-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_985
-- name    : FiniteTriangular.sum_range_985
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T10:36:56.218887+00:00
-- url     : https://prove2.me/theorems/640f7744-918e-40f4-8886-f20b7408e522
-- title:
--   Sum of the nonnegative integers below 985
-- statement:
--   The sum of the integers from $0$ through $984$ equals $484620$, which is the triangular number $\\frac{985(984)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_985 : ∑ k ∈ range 985, k = 484620 := by sorry
end FiniteTriangular
