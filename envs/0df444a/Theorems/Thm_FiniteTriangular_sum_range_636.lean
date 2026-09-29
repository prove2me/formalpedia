-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_636
-- name    : FiniteTriangular.sum_range_636
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:51:39.807901+00:00
-- url     : https://prove2.me/theorems/7cddfaa6-b1b5-4ca8-971e-53d1b91148cd
-- title:
--   Sum of integers below 636
-- statement:
--   The sum of the nonnegative integers strictly less than $636$ equals $201930$. Equivalently, $\\sum_{k=0}^{636-1} k = 636(636-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_636 : ∑ k ∈ range 636, k = 201930 := by sorry

end FiniteTriangular
