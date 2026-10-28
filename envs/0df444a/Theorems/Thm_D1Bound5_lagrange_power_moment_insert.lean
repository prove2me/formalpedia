-- Prove2me | Theorems.Thm_D1Bound5_lagrange_power_moment_insert
-- name    : D1Bound5.lagrange_power_moment_insert
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:42:31.05602+00:00
-- url     : https://prove2.me/theorems/2285e8cb-8fe4-45cc-8cca-43a9bc1b9a37
-- title:
--   Lagrange power moment insert
-- statement:
--   The node-adjunction recurrence for every Lagrange power moment. The only separation hypothesis concerns the newly added node.
-- source:
--   D1Bound5/LagrangeAdjunction.lean, lines 39-67, SHA-256 8078b0e0b630a0efdfdb1b29b441485777d7118007ce69e74197ac884086e248. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.LinearAlgebra.Lagrange

section
open Polynomial Finset

namespace D1Bound5






theorem _root_.D1Bound5.lagrange_power_moment_insert
    {F ι : Type*} [Field F] [DecidableEq ι]
    (s : Finset ι) (a : ι → F) (t : ι)
    (ht : t ∉ s) (hsep : ∀ i ∈ s, a i ≠ a t)
    (n : ℕ) :
    (∑ i ∈ insert t s,
      (a i) ^ (n + 1) / (∏ j ∈ (insert t s).erase i, (a i - a j))) =
      a t * (∑ i ∈ insert t s,
        (a i) ^ n / (∏ j ∈ (insert t s).erase i, (a i - a j))) +
      (∑ i ∈ s,
        (a i) ^ n / (∏ j ∈ s.erase i, (a i - a j))) := by sorry

end D1Bound5
end
