-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_115
-- name    : FiniteTriangular.sum_range_115
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:49:08.663236+00:00
-- url     : https://prove2.me/theorems/9b1c06b7-93ca-4e58-a5ad-ea60ba4d63b5
-- title:
--   Sum of integers below 115
-- statement:
--   The sum of the nonnegative integers strictly less than $115$ equals $6555$. Equivalently, $\sum_{k=0}^{115-1} k = 115(115-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_115 : ∑ k ∈ range 115, k = 6555 := by sorry

end FiniteTriangular
