-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1037
-- name    : FiniteTriangular.sum_range_1037
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T10:47:40.706814+00:00
-- url     : https://prove2.me/theorems/8d50aad3-e917-435f-b7a5-7a4efe6d104b
-- title:
--   Sum of the nonnegative integers below 1037
-- statement:
--   The sum of the integers from $0$ through $1036$ equals $537166$, which is the triangular number $\\frac{1037(1036)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1037 : ∑ k ∈ range 1037, k = 537166 := by sorry
end FiniteTriangular
