-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1025
-- name    : FiniteTriangular.sum_range_1025
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T10:45:48.370985+00:00
-- url     : https://prove2.me/theorems/8ec0ef0b-28bd-4f69-a294-dbeadedec94f
-- title:
--   Sum of the nonnegative integers below 1025
-- statement:
--   The sum of the integers from $0$ through $1024$ equals $524800$, which is the triangular number $\\frac{1025(1024)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1025 : ∑ k ∈ range 1025, k = 524800 := by sorry
end FiniteTriangular
