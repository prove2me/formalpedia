-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_223
-- name    : FiniteTriangular.sum_range_223
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T07:53:16.44635+00:00
-- url     : https://prove2.me/theorems/65e73c54-2660-4c29-ad80-74ce0ecc0e85
-- title:
--   Sum of integers below 223
-- statement:
--   The sum of the nonnegative integers strictly less than $223$ equals $24753$. Equivalently, $\\sum_{k=0}^{223-1} k = 223(223-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_223 : ∑ k ∈ range 223, k = 24753 := by sorry

end FiniteTriangular
