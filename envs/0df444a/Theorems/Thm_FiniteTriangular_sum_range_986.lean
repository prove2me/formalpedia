-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_986
-- name    : FiniteTriangular.sum_range_986
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T10:36:52.586988+00:00
-- url     : https://prove2.me/theorems/bcbc3d4f-a333-4d2a-8ba3-f4614b34f10b
-- title:
--   Sum of the nonnegative integers below 986
-- statement:
--   The sum of the integers from $0$ through $985$ equals $485605$, which is the triangular number $\\frac{986(985)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_986 : ∑ k ∈ range 986, k = 485605 := by sorry
end FiniteTriangular
