-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_164
-- name    : FiniteTriangular.sum_range_164
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T20:00:50.613773+00:00
-- url     : https://prove2.me/theorems/ec17b0ed-231c-4dd9-b310-070698b4133d
-- title:
--   Sum of integers below 164
-- statement:
--   The sum of the nonnegative integers strictly less than $164$ equals $13366$. Equivalently, $\sum_{k=0}^{164-1} k = 164(164-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_164 : ∑ k ∈ range 164, k = 13366 := by sorry

end FiniteTriangular
