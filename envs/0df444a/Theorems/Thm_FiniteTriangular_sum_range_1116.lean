-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1116
-- name    : FiniteTriangular.sum_range_1116
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T17:28:56.401672+00:00
-- url     : https://prove2.me/theorems/1aedc313-db94-41f2-a66e-bd7cc98be520
-- title:
--   Sum of the nonnegative integers below 1116
-- statement:
--   The sum of the integers from $0$ through $1115$ equals $622170$, which is the triangular number $\\frac{1116(1115)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1116 : ∑ k ∈ range 1116, k = 622170 := by sorry
end FiniteTriangular
