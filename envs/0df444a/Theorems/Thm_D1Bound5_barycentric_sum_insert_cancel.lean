-- Prove2me | Theorems.Thm_D1Bound5_barycentric_sum_insert_cancel
-- name    : D1Bound5.barycentric_sum_insert_cancel
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:27:22.974495+00:00
-- url     : https://prove2.me/theorems/fd2a5db2-15c6-4a5e-9a74-42a167618db7
-- title:
--   Barycentric sum insert cancel
-- statement:
--   Multiplication of arbitrary nodal data by the new-node difference removes that node from the barycentric sum. Old node values may coincide.
-- source:
--   D1Bound5/LagrangeAdjunction.lean, lines 20-37, SHA-256 8078b0e0b630a0efdfdb1b29b441485777d7118007ce69e74197ac884086e248. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.LinearAlgebra.Lagrange

section
open Polynomial Finset

namespace D1Bound5




theorem _root_.D1Bound5.barycentric_sum_insert_cancel
    {F ι : Type*} [Field F] [DecidableEq ι]
    (s : Finset ι) (a g : ι → F) (t : ι)
    (ht : t ∉ s) (hsep : ∀ i ∈ s, a i ≠ a t) :
    (∑ i ∈ insert t s,
      ((a i - a t) * g i) /
        (∏ j ∈ (insert t s).erase i, (a i - a j))) =
      ∑ i ∈ s, g i / (∏ j ∈ s.erase i, (a i - a j)) := by sorry



end D1Bound5
end
