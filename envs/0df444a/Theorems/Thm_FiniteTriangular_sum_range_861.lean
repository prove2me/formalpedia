-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_861
-- name    : FiniteTriangular.sum_range_861
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:39:58.477629+00:00
-- url     : https://prove2.me/theorems/56d81307-996a-42a4-956a-fed8cba746ca
-- title:
--   Sum of integers below 861
-- statement:
--   The sum of the nonnegative integers strictly less than $861$ equals $370230$. Equivalently, $\\sum_{k=0}^{861-1} k = 861(861-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_861 : ∑ k ∈ range 861, k = 370230 := by sorry

end FiniteTriangular
