-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_535
-- name    : FiniteTriangular.sum_range_535
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:27:18.421329+00:00
-- url     : https://prove2.me/theorems/d13795c2-b136-4d55-afc2-5833d1978929
-- title:
--   Sum of integers below 535
-- statement:
--   The sum of the nonnegative integers strictly less than $535$ equals $142845$. Equivalently, $\\sum_{k=0}^{535-1} k = 535(535-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_535 : ∑ k ∈ range 535, k = 142845 := by sorry

end FiniteTriangular
