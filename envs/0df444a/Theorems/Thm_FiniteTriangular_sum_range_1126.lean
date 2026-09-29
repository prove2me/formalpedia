-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1126
-- name    : FiniteTriangular.sum_range_1126
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T17:30:35.098721+00:00
-- url     : https://prove2.me/theorems/894030ef-bc4a-4cc2-8344-3dd98b69df9b
-- title:
--   Sum of the nonnegative integers below 1126
-- statement:
--   The sum of the integers from $0$ through $1125$ equals $633375$, which is the triangular number $\\frac{1126(1125)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1126 : ∑ k ∈ range 1126, k = 633375 := by sorry
end FiniteTriangular
