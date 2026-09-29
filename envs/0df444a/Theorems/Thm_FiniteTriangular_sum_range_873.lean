-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_873
-- name    : FiniteTriangular.sum_range_873
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T11:43:29.876877+00:00
-- url     : https://prove2.me/theorems/b086399e-c631-46fd-88f2-2a1ecf9c06b5
-- title:
--   Sum of integers below 873
-- statement:
--   The sum of the nonnegative integers strictly less than $873$ equals $380628$. Equivalently, $\\sum_{k=0}^{873-1} k = 873(873-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_873 : ∑ k ∈ range 873, k = 380628 := by sorry

end FiniteTriangular
