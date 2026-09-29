-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_823
-- name    : FiniteTriangular.sum_range_823
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:31:46.748499+00:00
-- url     : https://prove2.me/theorems/f36deb42-a473-43fa-a3e0-cd37da63b4ed
-- title:
--   Sum of integers below 823
-- statement:
--   The sum of the nonnegative integers strictly less than $823$ equals $338253$. Equivalently, $\\sum_{k=0}^{823-1} k = 823(823-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_823 : ∑ k ∈ range 823, k = 338253 := by sorry

end FiniteTriangular
