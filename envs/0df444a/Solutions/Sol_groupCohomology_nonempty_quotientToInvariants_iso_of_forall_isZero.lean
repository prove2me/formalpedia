-- Prove2me | solution 1 for groupCohomology.nonempty_quotientToInvariants_iso_of_forall_isZero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/2fff785c-b9f4-5cd1-ba5b-55f928bcd8a1

import Mathlib
import Theorems.Thm_groupCohomology_inf_injective_and_exact_of_isZero_res
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_nonempty_quotientToInvariants_iso_of_forall_isZero

set_option autoImplicit false
universe u
open CategoryTheory groupCohomology Rep
set_option maxHeartbeats 1600000

theorem solution {k G : Type u} [CommRing k] [Group G]
    (N : Subgroup G) [N.Normal] (A : Rep.{u} k G)
    (hN : ∀ i : ℕ, CategoryTheory.Limits.IsZero (groupCohomology (Rep.res N.subtype A) (i + 1))) (n : ℕ) :
    Nonempty (groupCohomology (A.quotientToInvariants N) (n + 1) ≅ groupCohomology A (n + 1)) := by
  classical
  obtain ⟨hinj, hex⟩ := groupCohomology.inf_injective_and_exact_of_isZero_res A N (n + 1)
    (fun i hi _ => by
      obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      exact hN j)
  have hsurj : Function.Surjective (groupCohomology.map (A := A.quotientToInvariants N) (B := A)
      (QuotientGroup.mk' N) (Rep.ofHom (A.ρ.quotientToInvariants_lift N)) (n + 1)).hom := by
    intro x
    have hz : ∀ y : groupCohomology (Rep.res N.subtype A) (n + 1), y = 0 := fun y => by
      simpa using congrArg (fun φ : groupCohomology (Rep.res N.subtype A) (n + 1) ⟶ _ => φ.hom y)
        ((hN n).eq_of_src (𝟙 _) 0)
    exact hex x (hz _)
  exact ⟨(LinearEquiv.ofBijective _ ⟨hinj, hsurj⟩).toModuleIso⟩

end S_groupCohomology_nonempty_quotientToInvariants_iso_of_forall_isZero
end P2MW
export P2MW.S_groupCohomology_nonempty_quotientToInvariants_iso_of_forall_isZero (solution)
