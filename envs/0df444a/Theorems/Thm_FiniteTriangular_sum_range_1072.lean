-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_1072
-- name    : FiniteTriangular.sum_range_1072
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-26T17:18:40.044692+00:00
-- url     : https://prove2.me/theorems/b75a30a5-879f-4306-8d5f-dbcd4e3f3560
-- title:
--   Sum of the nonnegative integers below 1072
-- statement:
--   The sum of the integers from $0$ through $1071$ equals $574056$, which is the triangular number $\\frac{1072(1071)}{2}$.
-- source:
--   The closed form for the sum of an initial segment of the nonnegative integers.

import Mathlib
open Finset

namespace FiniteTriangular
theorem sum_range_1072 : ∑ k ∈ range 1072, k = 574056 := by sorry
end FiniteTriangular
