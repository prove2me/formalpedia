-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_446
-- name    : FiniteTriangular.sum_range_446
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:08:03.735745+00:00
-- url     : https://prove2.me/theorems/3f0437c5-abc5-4959-8db6-8edd5b19622b
-- title:
--   Sum of integers below 446
-- statement:
--   The sum of the nonnegative integers strictly less than $446$ equals $99235$. Equivalently, $\\sum_{k=0}^{446-1} k = 446(446-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_446 : ∑ k ∈ range 446, k = 99235 := by sorry

end FiniteTriangular
