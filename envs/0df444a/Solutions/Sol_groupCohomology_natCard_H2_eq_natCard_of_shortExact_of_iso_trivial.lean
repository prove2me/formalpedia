-- Prove2me | solution 1 for groupCohomology.natCard_H2_eq_natCard_of_shortExact_of_iso_trivial
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/e17f2751-f2ae-5455-b886-b74bfeba5067

import Mathlib
import Theorems.Thm_groupCohomology_subsingleton_H1_trivial_int
import Theorems.Thm_groupCohomology_natCard_H2_trivial_int
import Theorems.Thm_groupCohomology_finite_H2_of_shortExact
import Theorems.Thm_groupCohomology_natCard_H2_mul_of_shortExact
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_natCard_H2_eq_natCard_of_shortExact_of_iso_trivial

set_option autoImplicit false

universe u

open CategoryTheory groupCohomology
open Rep.FiniteCyclicGroup

theorem solution
    {G : Type} [Group G] [Finite G] [IsCyclic G]
    {X : ShortComplex (Rep ℤ G)} (hX : X.ShortExact) (e : X.X₃ ≅ Rep.trivial ℤ G ℤ)
    [Finite (H1 X.X₁)] [Finite (H2 X.X₁)] (h1 : Nat.card (H1 X.X₁) = Nat.card (H2 X.X₁))
    [Subsingleton (H1 X.X₂)] :
    Finite (H2 X.X₂) ∧ Nat.card (H2 X.X₂) = Nat.card G := by

  have e1 := ((groupCohomology.functor ℤ G 1).mapIso e).toLinearEquiv.toEquiv
  have e2 := ((groupCohomology.functor ℤ G 2).mapIso e).toLinearEquiv.toEquiv
  haveI : Subsingleton (H1 X.X₃) := by
    haveI : Subsingleton ((groupCohomology.functor ℤ G 1).obj (Rep.trivial ℤ G ℤ)) :=
      subsingleton_H1_trivial_int (G := G)
    exact e1.subsingleton
  have h23 : Nat.card (H2 X.X₃) = Nat.card G :=
    (Nat.card_congr e2).trans (natCard_H2_trivial_int (G := G))
  haveI : Finite (H1 X.X₃) := Finite.of_subsingleton
  haveI : Finite (H2 X.X₃) := Nat.finite_of_card_ne_zero (by rw [h23]; exact Nat.card_pos.ne')
  haveI : Finite (H1 X.X₂) := Finite.of_subsingleton
  haveI hF2 : Finite (H2 X.X₂) := finite_H2_of_shortExact hX
  refine ⟨hF2, ?_⟩
  have h := natCard_H2_mul_of_shortExact hX
  have hu2 : Nat.card (H1 X.X₂) = 1 := Nat.card_eq_one_iff_unique.2 ⟨inferInstance, ⟨0⟩⟩
  have hu3 : Nat.card (H1 X.X₃) = 1 := Nat.card_eq_one_iff_unique.2 ⟨inferInstance, ⟨0⟩⟩
  rw [hu2, hu3, mul_one, one_mul, h1, h23, mul_comm (Nat.card (H2 X.X₁))] at h
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h

end S_groupCohomology_natCard_H2_eq_natCard_of_shortExact_of_iso_trivial
end P2MW
export P2MW.S_groupCohomology_natCard_H2_eq_natCard_of_shortExact_of_iso_trivial (solution)
