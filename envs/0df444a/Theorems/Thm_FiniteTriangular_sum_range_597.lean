-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_597
-- name    : FiniteTriangular.sum_range_597
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:42:57.856429+00:00
-- url     : https://prove2.me/theorems/6249291e-fc24-4837-9f88-2a7642b40a48
-- title:
--   Sum of integers below 597
-- statement:
--   The sum of the nonnegative integers strictly less than $597$ equals $177906$. Equivalently, $\\sum_{k=0}^{597-1} k = 597(597-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_597 : ∑ k ∈ range 597, k = 177906 := by sorry

end FiniteTriangular
