-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_904
-- name    : FiniteTriangular.sum_range_904
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:48:38.950433+00:00
-- url     : https://prove2.me/theorems/cce34f71-9eb7-4279-a1af-54328bf55352
-- title:
--   Sum of integers below 904
-- statement:
--   The sum of the nonnegative integers strictly less than $904$ equals $408156$. Equivalently, $\\sum_{k=0}^{904-1} k = 904(904-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_904 : ∑ k ∈ range 904, k = 408156 := by sorry

end FiniteTriangular
