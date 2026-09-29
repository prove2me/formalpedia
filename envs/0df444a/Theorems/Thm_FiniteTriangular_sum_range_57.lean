-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_57
-- name    : FiniteTriangular.sum_range_57
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T19:19:02.714992+00:00
-- url     : https://prove2.me/theorems/326e957d-cc8e-4a29-9449-705ec44018c4
-- title:
--   Sum of integers below 57
-- statement:
--   The sum of the nonnegative integers strictly less than $57$ equals $1596$. Equivalently, $\sum_{k=0}^{57-1} k = 57(57-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_57 : ∑ k ∈ range 57, k = 1596 := by sorry

end FiniteTriangular
