-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1051
-- name    : FiniteTriangular.sum_range_1051
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T17:14:52.147717+00:00
-- url     : https://prove2.me/theorems/121dec17-8265-4b05-920f-f24236dd2353
-- title:
--   Sum of the nonnegative integers below 1051
-- statement:
--   The sum of the integers from $0$ through $1050$ equals $551775$, which is the triangular number $\\frac{1051(1050)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1051 : ∑ k ∈ range 1051, k = 551775 := by sorry
end FiniteTriangular
