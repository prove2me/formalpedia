-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_537
-- name    : FiniteTriangular.sum_range_537
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:28:53.781636+00:00
-- url     : https://prove2.me/theorems/49c20ce9-ebd0-432f-b661-0a1ddd4d9e69
-- title:
--   Sum of integers below 537
-- statement:
--   The sum of the nonnegative integers strictly less than $537$ equals $143916$. Equivalently, $\\sum_{k=0}^{537-1} k = 537(537-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_537 : ∑ k ∈ range 537, k = 143916 := by sorry

end FiniteTriangular
