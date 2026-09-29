-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_174
-- name    : FiniteTriangular.sum_range_174
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T20:02:22.399033+00:00
-- url     : https://prove2.me/theorems/3a111c91-e4b8-4ffe-9871-5580134c721b
-- title:
--   Sum of integers below 174
-- statement:
--   The sum of the nonnegative integers strictly less than $174$ equals $15051$. Equivalently, $\sum_{k=0}^{174-1} k = 174(174-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_174 : ∑ k ∈ range 174, k = 15051 := by sorry

end FiniteTriangular
