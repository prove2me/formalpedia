-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_5
-- name    : FiniteTriangular.sum_range_5
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T18:55:51.137985+00:00
-- url     : https://prove2.me/theorems/2d18dccc-971e-4d2d-b7b4-b1569870433e
-- title:
--   Sum of range 5
-- statement:
--   The sum of the nonnegative integers $k$ with $0 \le k < 5$ equals the triangular number $10 = 5(5-1)/2$.
-- source:
--   Elementary arithmetic series: $\sum_{k=0}^{n-1} k = n(n-1)/2$.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_5 : ∑ k ∈ range 5, k = 10 := by sorry

end FiniteTriangular
