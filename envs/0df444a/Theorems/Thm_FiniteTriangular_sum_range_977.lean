-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_977
-- name    : FiniteTriangular.sum_range_977
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T10:34:58.417893+00:00
-- url     : https://prove2.me/theorems/47e178f4-d2fe-4f1a-aeee-cb471917ba9b
-- title:
--   Sum of the nonnegative integers below 977
-- statement:
--   The sum of the integers from $0$ through $976$ equals $476776$, which is the triangular number $\\frac{977(976)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_977 : ∑ k ∈ range 977, k = 476776 := by sorry
end FiniteTriangular
