-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_76
-- name    : FiniteTriangular.sum_range_76
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:38:12.150503+00:00
-- url     : https://prove2.me/theorems/f5fdb2b9-2b49-4fea-ab1d-7c499e67723d
-- title:
--   Sum of integers below 76
-- statement:
--   The sum of the nonnegative integers strictly less than $76$ equals $2850$. Equivalently, $\sum_{k=0}^{76-1} k = 76(76-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_76 : ∑ k ∈ range 76, k = 2850 := by sorry

end FiniteTriangular
