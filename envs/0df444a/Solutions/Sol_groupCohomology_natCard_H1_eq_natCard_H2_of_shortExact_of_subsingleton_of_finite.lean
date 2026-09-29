-- Prove2me | solution 1 for groupCohomology.natCard_H1_eq_natCard_H2_of_shortExact_of_subsingleton_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/462077ce-fba1-549e-a77e-26497fc2f689

import Mathlib
import Theorems.Thm_groupCohomology_natCard_H1_eq_natCard_H2_of_finite
import Theorems.Thm_groupCohomology_finite_H1_of_shortExact
import Theorems.Thm_groupCohomology_finite_H2_of_shortExact
import Theorems.Thm_groupCohomology_natCard_H2_mul_of_shortExact
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_natCard_H1_eq_natCard_H2_of_shortExact_of_subsingleton_of_finite

set_option autoImplicit false

universe u

open CategoryTheory groupCohomology
open Rep.FiniteCyclicGroup

theorem solution
    {G : Type} [Group G] [Finite G] [IsCyclic G]
    {X : ShortComplex (Rep ℤ G)} (hX : X.ShortExact)
    [Subsingleton (H1 X.X₁)] [Subsingleton (H2 X.X₁)] [Finite X.X₃] :
    Finite (H1 X.X₂) ∧ Finite (H2 X.X₂) ∧ Nat.card (H1 X.X₂) = Nat.card (H2 X.X₂) := by
  obtain ⟨f1, f2, h3⟩ := natCard_H1_eq_natCard_H2_of_finite X.X₃
  haveI := f1
  haveI := f2
  haveI : Finite (H1 X.X₁) := Finite.of_subsingleton
  haveI : Finite (H2 X.X₁) := Finite.of_subsingleton
  haveI hF1 : Finite (H1 X.X₂) := finite_H1_of_shortExact hX
  haveI hF2 : Finite (H2 X.X₂) := finite_H2_of_shortExact hX
  refine ⟨hF1, hF2, ?_⟩
  have h := natCard_H2_mul_of_shortExact hX
  have h1 : Nat.card (H1 X.X₁) = 1 := Nat.card_eq_one_iff_unique.2 ⟨inferInstance, ⟨0⟩⟩
  have h2 : Nat.card (H2 X.X₁) = 1 := Nat.card_eq_one_iff_unique.2 ⟨inferInstance, ⟨0⟩⟩
  rw [h1, h2, mul_one, mul_one, h3] at h
  exact (Nat.eq_of_mul_eq_mul_right Nat.card_pos h).symm

end S_groupCohomology_natCard_H1_eq_natCard_H2_of_shortExact_of_subsingleton_of_finite
end P2MW
export P2MW.S_groupCohomology_natCard_H1_eq_natCard_H2_of_shortExact_of_subsingleton_of_finite (solution)
