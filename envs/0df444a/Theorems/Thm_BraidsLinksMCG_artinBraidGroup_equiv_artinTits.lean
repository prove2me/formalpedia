-- Prove2me | Theorems.Thm_BraidsLinksMCG_artinBraidGroup_equiv_artinTits
-- name    : BraidsLinksMCG.artinBraidGroup_equiv_artinTits
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-20T20:00:23.702175+00:00
-- url     : https://prove2.me/theorems/034c6bb0-0c2a-4b07-8212-73ddd8b7c431
-- title:
--   The platform braid group is the Artin-Tits group of type A
-- statement:
--   The braid group on `n` strands is presented on this platform by a hand-written relator set,
--   `BraidsLinksMCG.braidRels n`: the commuting relators `σᵢ σⱼ σᵢ⁻¹ σⱼ⁻¹` for `|i - j| ≥ 2`, and the
--   braid relators `σᵢ σⱼ σᵢ (σⱼ σᵢ σⱼ)⁻¹` for `j = i + 1`.
--
--   The standard object is the **Artin–Tits group** (generalised braid group) of a Coxeter matrix `M`:
--   the group on the same generators subject only to `braidWord M i i' = braidWord M i' i`, where
--   `CoxeterSystem.braidWord M i i'` is the word of length `M i i'` alternating between `i` and `i'`.
--   Taking `M = CoxeterMatrix.A (n - 1)` gives the braid group on `n` strands.
--
--   This milestone asserts that the two presentations define the same group, matching the generators.
--   It is the bridge that lets the standard Coxeter/Artin–Tits theory be applied to
--   `ArtinBraidGroup`, which is otherwise an isolated ad-hoc presentation.
--
--   The relators in fact coincide on the nose. For `M i j = 2` (indices at distance at least two)
--   `braidWord M i j = [i, j]`, so the relator is `σᵢ σⱼ σᵢ⁻¹ σⱼ⁻¹` — verbatim the platform's
--   commuting relator. For `M i j = 3` (adjacent indices) `braidWord M j i = [i, j, i]`, giving the
--   platform's braid relator. The remaining Artin–Tits relators are accounted for by the diagonal
--   (`M i i = 1` makes the relator trivial) and by the opposite adjacency ordering, which contributes
--   the inverse of a platform relator.
-- source:
--   Artin-Tits presentation of the braid group of type A; approach after TauCetiProject/TauCeti, GroupTheory/Coxeter/Artin.lean and GroupTheory/SpecificGroups/Braid.lean (https://github.com/TauCetiProject/TauCeti, Apache-2.0). Stated against Mathlib's CoxeterSystem.braidWord and CoxeterMatrix.A.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup

open CoxeterSystem

namespace BraidsLinksMCG

/-- The hand-written presentation `ArtinBraidGroup n` agrees with the Artin–Tits
(generalised braid) group of the Coxeter matrix of type `A`, whose relators are the two
alternating `braidWord`s of `CoxeterMatrix.A (n - 1)` set against each other. -/
theorem artinBraidGroup_equiv_artinTits (n : ℕ) :
    Nonempty (ArtinBraidGroup n ≃*
      PresentedGroup (Set.range (Function.uncurry
        (fun i i' : Fin (n - 1) =>
          ((braidWord (CoxeterMatrix.A (n - 1)) i i').map FreeGroup.of).prod *
            (((braidWord (CoxeterMatrix.A (n - 1)) i' i).map FreeGroup.of).prod)⁻¹)))) := by
  sorry

end BraidsLinksMCG
