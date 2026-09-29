-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_648
-- name    : FiniteTriangular.sum_range_648
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:53:12.831879+00:00
-- url     : https://prove2.me/theorems/e54c9337-86ca-4858-9574-36ed9117dbc2
-- title:
--   Sum of integers below 648
-- statement:
--   The sum of the nonnegative integers strictly less than $648$ equals $209628$. Equivalently, $\\sum_{k=0}^{648-1} k = 648(648-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_648 : ∑ k ∈ range 648, k = 209628 := by sorry

end FiniteTriangular
