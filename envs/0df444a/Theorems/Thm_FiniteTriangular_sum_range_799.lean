-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_799
-- name    : FiniteTriangular.sum_range_799
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:26:34.36871+00:00
-- url     : https://prove2.me/theorems/840fc8b1-3a9a-4a95-abd1-4bfb9e41f39c
-- title:
--   Sum of integers below 799
-- statement:
--   The sum of the nonnegative integers strictly less than $799$ equals $318801$. Equivalently, $\\sum_{k=0}^{799-1} k = 799(799-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_799 : ∑ k ∈ range 799, k = 318801 := by sorry

end FiniteTriangular
