-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_84
-- name    : FiniteTriangular.sum_range_84
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:40:01.681167+00:00
-- url     : https://prove2.me/theorems/f4f7e6b3-2881-49ea-9b29-175521369acb
-- title:
--   Sum of integers below 84
-- statement:
--   The sum of the nonnegative integers strictly less than $84$ equals $3486$. Equivalently, $\sum_{k=0}^{84-1} k = 84(84-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_84 : ∑ k ∈ range 84, k = 3486 := by sorry

end FiniteTriangular
