-- Prove2me | Theorems.Thm_D1Bound5_barycentric_denominator_insert
-- name    : D1Bound5.barycentric_denominator_insert
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:27:46.503161+00:00
-- url     : https://prove2.me/theorems/0cb4031b-02b3-4352-8dc2-4cdac248c1ea
-- title:
--   Barycentric denominator insert
-- statement:
--   An old barycentric denominator acquires the new-node difference.
-- source:
--   D1Bound5/LagrangeAdjunction.lean, lines 7-18, SHA-256 8078b0e0b630a0efdfdb1b29b441485777d7118007ce69e74197ac884086e248. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.LinearAlgebra.Lagrange

section
open Polynomial Finset

namespace D1Bound5


theorem _root_.D1Bound5.barycentric_denominator_insert
    {F ι : Type*} [Field F] [DecidableEq ι]
    (s : Finset ι) (a : ι → F) (t i : ι)
    (ht : t ∉ s) (hi : i ∈ s) :
    (∏ j ∈ (insert t s).erase i, (a i - a j)) =
      (a i - a t) * ∏ j ∈ s.erase i, (a i - a j) := by sorry





end D1Bound5
end
