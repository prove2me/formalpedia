-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_682
-- name    : FiniteTriangular.sum_range_682
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:01:46.406302+00:00
-- url     : https://prove2.me/theorems/cf1f3b91-dff8-48cc-85d1-b034eec550dd
-- title:
--   Sum of integers below 682
-- statement:
--   The sum of the nonnegative integers strictly less than $682$ equals $232221$. Equivalently, $\\sum_{k=0}^{682-1} k = 682(682-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_682 : ∑ k ∈ range 682, k = 232221 := by sorry

end FiniteTriangular
