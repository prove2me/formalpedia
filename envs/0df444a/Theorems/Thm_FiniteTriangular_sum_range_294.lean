-- Prove2me | Theorems.Thm_FiniteTriangular_sum_range_294
-- name    : FiniteTriangular.sum_range_294
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T08:18:08.869474+00:00
-- url     : https://prove2.me/theorems/e104e8fd-f760-42e6-b801-d9aeeeb49bdd
-- title:
--   Sum of integers below 294
-- statement:
--   The sum of the nonnegative integers strictly less than $294$ equals $43071$. Equivalently, $\\sum_{k=0}^{294-1} k = 294(294-1)/2$.
-- source:
--   Elementary arithmetic series: the sum of the first m positive integers is m(m+1)/2, rewritten on Finset.range.

import Mathlib
open Finset

namespace FiniteTriangular

theorem sum_range_294 : ∑ k ∈ range 294, k = 43071 := by sorry

end FiniteTriangular
