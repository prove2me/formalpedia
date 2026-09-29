-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_993
-- name    : FiniteTriangular.sum_range_993
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T10:38:42.23997+00:00
-- url     : https://prove2.me/theorems/db1912b6-5365-4907-a949-325b0623edab
-- title:
--   Sum of the nonnegative integers below 993
-- statement:
--   The sum of the integers from $0$ through $992$ equals $492528$, which is the triangular number $\\frac{993(992)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_993 : ∑ k ∈ range 993, k = 492528 := by sorry
end FiniteTriangular
