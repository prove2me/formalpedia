-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_866
-- name    : FiniteTriangular.sum_range_866
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:41:46.243352+00:00
-- url     : https://prove2.me/theorems/c2912f42-1a94-4b4d-b3cb-69d91cf1efb8
-- title:
--   Sum of integers below 866
-- statement:
--   The sum of the nonnegative integers strictly less than $866$ equals $374545$. Equivalently, $\\sum_{k=0}^{866-1} k = 866(866-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_866 : ∑ k ∈ range 866, k = 374545 := by sorry

end FiniteTriangular
