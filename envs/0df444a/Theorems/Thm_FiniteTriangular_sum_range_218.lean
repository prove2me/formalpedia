-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_218
-- name    : FiniteTriangular.sum_range_218
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T07:53:16.965619+00:00
-- url     : https://prove2.me/theorems/d7126b9a-132f-44c2-b4c1-51524649ba7b
-- title:
--   Sum of integers below 218
-- statement:
--   The sum of the nonnegative integers strictly less than $218$ equals $23653$. Equivalently, $\\sum_{k=0}^{218-1} k = 218(218-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_218 : ∑ k ∈ range 218, k = 23653 := by sorry

end FiniteTriangular
