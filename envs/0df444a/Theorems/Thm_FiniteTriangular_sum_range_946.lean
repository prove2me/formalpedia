-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_946
-- name    : FiniteTriangular.sum_range_946
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:58:56.355782+00:00
-- url     : https://prove2.me/theorems/ecf874f8-8acf-4ba9-84b8-3cfd76dd7b14
-- title:
--   Sum of integers below 946
-- statement:
--   The sum of the nonnegative integers strictly less than $946$ equals $446985$. Equivalently, $\\sum_{k=0}^{946-1} k = 946(946-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_946 : ∑ k ∈ range 946, k = 446985 := by sorry

end FiniteTriangular
