-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_308
-- name    : FiniteTriangular.sum_range_308
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T08:21:52.544928+00:00
-- url     : https://prove2.me/theorems/345b4c51-4aa8-49b6-9c1e-546e138942e2
-- title:
--   Sum of integers below 308
-- statement:
--   The sum of the nonnegative integers strictly less than $308$ equals $47278$. Equivalently, $\\sum_{k=0}^{308-1} k = 308(308-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_308 : ∑ k ∈ range 308, k = 47278 := by sorry

end FiniteTriangular
