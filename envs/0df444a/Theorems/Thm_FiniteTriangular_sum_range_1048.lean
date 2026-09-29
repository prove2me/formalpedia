-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1048
-- name    : FiniteTriangular.sum_range_1048
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T17:13:11.726065+00:00
-- url     : https://prove2.me/theorems/042f3ed7-8a78-41b4-94fd-30cea7dde600
-- title:
--   Sum of the nonnegative integers below 1048
-- statement:
--   The sum of the integers from $0$ through $1047$ equals $548628$, which is the triangular number $\\frac{1048(1047)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1048 : ∑ k ∈ range 1048, k = 548628 := by sorry
end FiniteTriangular
