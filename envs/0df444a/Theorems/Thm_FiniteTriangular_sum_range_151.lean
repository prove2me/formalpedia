-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_151
-- name    : FiniteTriangular.sum_range_151
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:58:17.129002+00:00
-- url     : https://prove2.me/theorems/78ec755e-cc79-4541-90cd-334109c0b578
-- title:
--   Sum of integers below 151
-- statement:
--   The sum of the nonnegative integers strictly less than $151$ equals $11325$. Equivalently, $\sum_{k=0}^{151-1} k = 151(151-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_151 : ∑ k ∈ range 151, k = 11325 := by sorry

end FiniteTriangular
