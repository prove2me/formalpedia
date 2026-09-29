-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_835
-- name    : FiniteTriangular.sum_range_835
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:35:08.833968+00:00
-- url     : https://prove2.me/theorems/3db9719d-08be-4389-9ba1-3c62c75de5ad
-- title:
--   Sum of integers below 835
-- statement:
--   The sum of the nonnegative integers strictly less than $835$ equals $348195$. Equivalently, $\\sum_{k=0}^{835-1} k = 835(835-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_835 : ∑ k ∈ range 835, k = 348195 := by sorry

end FiniteTriangular
