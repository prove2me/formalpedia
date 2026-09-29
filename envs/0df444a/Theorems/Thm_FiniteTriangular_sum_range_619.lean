-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_619
-- name    : FiniteTriangular.sum_range_619
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:48:08.131794+00:00
-- url     : https://prove2.me/theorems/a30896a1-e0c3-405c-930e-89cc74682df2
-- title:
--   Sum of integers below 619
-- statement:
--   The sum of the nonnegative integers strictly less than $619$ equals $191271$. Equivalently, $\\sum_{k=0}^{619-1} k = 619(619-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_619 : ∑ k ∈ range 619, k = 191271 := by sorry

end FiniteTriangular
