-- Prove2me | solution 1 for groupCohomology.subsingleton_H1_trivial_int
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/428f31c4-ea6b-599a-bfab-ab3c490199ff

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_subsingleton_H1_trivial_int

set_option autoImplicit false

universe u

open CategoryTheory groupCohomology
open Rep.FiniteCyclicGroup

theorem solution
    {G : Type} [Group G] [Finite G] :
    Subsingleton (H1 (Rep.trivial ℤ G ℤ)) := by
  haveI : Subsingleton (Additive G →+ ℤ) := by
    refine ⟨fun f₁ f₂ => AddMonoidHom.ext fun x => ?_⟩
    have h : ∀ f : Additive G →+ ℤ, f x = 0 := fun f => by
      have h1 : (Nat.card (Additive G)) • f x = 0 := by
        rw [← map_nsmul, card_nsmul_eq_zero', map_zero]
      rcases (by simpa [nsmul_eq_mul] using h1 : Nat.card (Additive G) = 0 ∨ f x = 0) with h2 | h2
      · exact absurd h2 Nat.card_pos.ne'
      · exact h2
    rw [h f₁, h f₂]
  exact (H1IsoOfIsTrivial (Rep.trivial ℤ G ℤ)).toLinearEquiv.toEquiv.subsingleton

end S_groupCohomology_subsingleton_H1_trivial_int
end P2MW
export P2MW.S_groupCohomology_subsingleton_H1_trivial_int (solution)
