-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1035
-- name    : FiniteTriangular.sum_range_1035
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T10:47:41.634984+00:00
-- url     : https://prove2.me/theorems/a465a104-c600-41e9-b123-e52699405ac4
-- title:
--   Sum of the nonnegative integers below 1035
-- statement:
--   The sum of the integers from $0$ through $1034$ equals $535095$, which is the triangular number $\\frac{1035(1034)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1035 : ∑ k ∈ range 1035, k = 535095 := by sorry
end FiniteTriangular
