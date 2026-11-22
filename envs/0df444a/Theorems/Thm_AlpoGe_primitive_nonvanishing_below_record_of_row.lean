-- Prove2me | Theorems.Thm_AlpoGe_primitive_nonvanishing_below_record_of_row
-- name    : AlpoGe.primitive_nonvanishing_below_record_of_row
-- status  : Open
-- author  : @GeorgeCoote
-- created : 2026-11-21T21:05:59.441442+00:00
-- url     : https://prove2.me/theorems/fed98188-9fd8-4c13-b49d-5f90b48e16ba
-- title:
--   Alpoge Row0b implies primitive Dirichlet nonvanishing below the verified boundary
-- statement:
--   Assume the Galois representation and local–global compatibility statement Row0b from L. Alpöge’s Lean release, with local reciprocity constrained by the release’s IsRecT laws. Let N be a positive integer and let $\chi$ be a primitive complex Dirichlet character modulo N. For every $s\in\mathbb C$ with $1/2<\operatorname{Re}s\le 0.8749570698$,
--   $$
--   L(\chi,s)\ne 0.
--   $$
--
--   This is the restriction of the release’s conditional nonvanishing assertion to primitive characters and to the range outside the independently verified strict half-plane bound. The character of conductor one is included, as is the upper endpoint of the displayed range.
-- source:
--   Restriction of L. Alpöge (with Claude), 20 November 2026 Lean release, UpperTheory.FinalTheorems.everyCharacter_of_row in CharacterBoxes/MainConclusion.lean, https://github.com/leanprover-community/riemann-hypothesis/blob/main/src/Development/AutomorphicArithmetic/CharacterBoxes/MainConclusion.lean. The upper endpoint comes from the strict bound https://prove2.me/theorems/3a8f3264-d5ab-422c-8e4f-a2c0e27d6918.

import Definitions.Def_AlpoGeB008

namespace AlpoGe

theorem primitive_nonvanishing_below_record_of_row
    (H : UpperTheory.GalStar.Row0b fun h rc => UpperTheory.Zero.LLC.IsRecT h rc) :
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
      ∀ s : ℂ, 1 / 2 < s.re → s.re ≤ (0.8749570698 : ℝ) →
        DirichletCharacter.LFunction χ s ≠ 0 := by
  sorry

end AlpoGe
