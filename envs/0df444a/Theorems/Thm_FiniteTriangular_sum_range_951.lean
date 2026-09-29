-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_951
-- name    : FiniteTriangular.sum_range_951
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:58:58.087234+00:00
-- url     : https://prove2.me/theorems/615b8fe0-3aa8-439e-9a42-c7626ddca4ac
-- title:
--   Sum of integers below 951
-- statement:
--   The sum of the nonnegative integers strictly less than $951$ equals $451725$. Equivalently, $\\sum_{k=0}^{951-1} k = 951(951-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_951 : ∑ k ∈ range 951, k = 451725 := by sorry

end FiniteTriangular
