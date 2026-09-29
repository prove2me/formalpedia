-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1000
-- name    : FiniteTriangular.sum_range_1000
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T10:38:44.806234+00:00
-- url     : https://prove2.me/theorems/d920fc33-d789-48c5-a36d-6b62cfe7663f
-- title:
--   Sum of the nonnegative integers below 1000
-- statement:
--   The sum of the integers from $0$ through $999$ equals $499500$, which is the triangular number $\\frac{1000(999)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1000 : ∑ k ∈ range 1000, k = 499500 := by sorry
end FiniteTriangular
