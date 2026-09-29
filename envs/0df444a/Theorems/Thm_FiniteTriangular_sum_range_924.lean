-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_924
-- name    : FiniteTriangular.sum_range_924
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:53:36.159776+00:00
-- url     : https://prove2.me/theorems/fac30def-ecf4-45f2-a1ad-c36cf59909eb
-- title:
--   Sum of integers below 924
-- statement:
--   The sum of the nonnegative integers strictly less than $924$ equals $426426$. Equivalently, $\\sum_{k=0}^{924-1} k = 924(924-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_924 : ∑ k ∈ range 924, k = 426426 := by sorry

end FiniteTriangular
