-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_994
-- name    : FiniteTriangular.sum_range_994
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T10:38:39.273984+00:00
-- url     : https://prove2.me/theorems/e90fab15-ee88-4d06-92a6-22f1e9179ea6
-- title:
--   Sum of the nonnegative integers below 994
-- statement:
--   The sum of the integers from $0$ through $993$ equals $493521$, which is the triangular number $\\frac{994(993)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_994 : ∑ k ∈ range 994, k = 493521 := by sorry
end FiniteTriangular
