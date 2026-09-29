-- Prove2me | solution 1 for groupCohomology.exists_continuousH2SrInflation_eq_of_nsmul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/cdad14f4-c074-583c-989e-8db93ea5aea6

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_LevelSubgroup
import Definitions.Def_GroupCohomology_ContinuousH2Inflation
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelInflation
import Theorems.Thm_groupCohomology_exists_continuousH2SrInflation_eq
import Theorems.Thm_groupCohomology_continuousH2SrInflation_H2pi_eq_zero_iff
import Theorems.Thm_groupCohomology_continuousH2SrInflation_H2pi_eq_of_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_exists_continuousH2SrInflation_eq_of_nsmul_eq_zero

set_option autoImplicit false
open CategoryTheory groupCohomology

namespace LimP

open CategoryTheory groupCohomology

variable {k G : Type} [CommRing k] [Group G]

lemma H2π_surjective (A : Rep.{0} k G) : Function.Surjective (H2π A) :=
  (ModuleCat.epi_iff_surjective (H2π A)).mp inferInstance

end LimP

open LimP in

theorem solution
    {k G : Type} [CommRing k] [Group G] (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (S : Finset Nat.Primes) (M : Rep.{0} k G)
    (hsm : ∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧ ∀ s : G, r s ∈ F.fixingSubgroup → M.ρ s m = m)
    (n : ℕ) (z : continuousH2Sr r S M) (hz : n • z = 0) :
    ∃ (F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hF : F.IsUnramifiedOutside S) (_ : IsGalois ℚ F)
      (y : H2 (M.quotientToInvariants (F.fixingSubgroup.comap r))),
      n • y = 0 ∧ continuousH2SrInflation r S M F hF y = z := by
  classical
  obtain ⟨F₁, hF₁, hG₁, y₁, hy₁⟩ := groupCohomology.exists_continuousH2SrInflation_eq r S M hsm z
  haveI : IsGalois ℚ ↥F₁ := hG₁
  obtain ⟨f, rfl⟩ := H2π_surjective _ y₁

  have h0 : continuousH2SrInflation r S M F₁ hF₁ (H2π _ (n • f)) = 0 := by
    rw [map_nsmul, map_nsmul, hy₁, hz]
  obtain ⟨F', hF', hG', hle, yc, hyc⟩ := (groupCohomology.continuousH2SrInflation_H2pi_eq_zero_iff r S M hsm F₁ hF₁ (n • f)).mp h0
  haveI : IsGalois ℚ ↥F' := hG'

  have hU : F'.fixingSubgroup.comap r ≤ F₁.fixingSubgroup.comap r :=
    fun s hs => IntermediateField.fixingSubgroup_antitone hle hs
  let π : G ⧸ F'.fixingSubgroup.comap r →* G ⧸ F₁.fixingSubgroup.comap r :=
    QuotientGroup.map _ _ (MonoidHom.id G) (fun s hs => hU hs)
  have hπ : ∀ g : G, π (g : G ⧸ F'.fixingSubgroup.comap r) = (g : G ⧸ F₁.fixingSubgroup.comap r) := fun g => rfl

  let fv : (G ⧸ F'.fixingSubgroup.comap r) × (G ⧸ F'.fixingSubgroup.comap r) → M.quotientToInvariants (F'.fixingSubgroup.comap r) :=
    fun ab => ⟨((f (π ab.1, π ab.2) : M.quotientToInvariants (F₁.fixingSubgroup.comap r)) : M),
      fun s => (f (π ab.1, π ab.2)).2 ⟨s.1, hU s.2⟩⟩
  have hfv : ∀ g h : G, ((fv ((g : G ⧸ F'.fixingSubgroup.comap r), (h : G ⧸ F'.fixingSubgroup.comap r)) : M.quotientToInvariants _) : M)
      = ((f ((g : G ⧸ F₁.fixingSubgroup.comap r), (h : G ⧸ F₁.fixingSubgroup.comap r)) : M.quotientToInvariants _) : M) := fun _ _ => rfl
  have hfv_mem : fv ∈ cocycles₂ (M.quotientToInvariants (F'.fixingSubgroup.comap r)) := by
    rw [mem_cocycles₂_iff]
    intro a b c
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective b
    obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective c
    have key := (mem_cocycles₂_iff (f : _ → _)).mp f.2 (g : G ⧸ F₁.fixingSubgroup.comap r) h j
    apply Subtype.ext
    have e1 : ((g : G ⧸ F'.fixingSubgroup.comap r) * (h : G ⧸ F'.fixingSubgroup.comap r)) = ((g * h : G) : G ⧸ F'.fixingSubgroup.comap r) := rfl
    have e2 : ((h : G ⧸ F'.fixingSubgroup.comap r) * (j : G ⧸ F'.fixingSubgroup.comap r)) = ((h * j : G) : G ⧸ F'.fixingSubgroup.comap r) := rfl
    rw [e1, e2]
    show ((f (π (g * h : G), π j) : M.quotientToInvariants _) : M) + ((f (π g, π h) : M.quotientToInvariants _) : M)
      = M.ρ g ((f (π h, π j) : M.quotientToInvariants _) : M) + ((f (π g, π (h * j : G)) : M.quotientToInvariants _) : M)
    simp only [hπ]
    exact congrArg Subtype.val key
  let f' : cocycles₂ (M.quotientToInvariants (F'.fixingSubgroup.comap r)) := ⟨fv, hfv_mem⟩
  have hff' : ∀ g h : G, ((f' ((g : G ⧸ F'.fixingSubgroup.comap r), (h : G ⧸ F'.fixingSubgroup.comap r)) : M.quotientToInvariants _) : M)
      = ((f ((g : G ⧸ F₁.fixingSubgroup.comap r), (h : G ⧸ F₁.fixingSubgroup.comap r)) : M.quotientToInvariants _) : M) := fun _ _ => rfl
  have hinf := groupCohomology.continuousH2SrInflation_H2pi_eq_of_le r S M F₁ F' hF₁ hF' f f' hff'
  refine ⟨F', hF', hG', H2π _ f', ?_, hinf.trans hy₁⟩

  rw [← map_nsmul, H2π_eq_zero_iff]
  refine ⟨yc, ?_⟩
  funext ab
  obtain ⟨a, b⟩ := ab
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective b
  rw [d₁₂_hom_apply]
  apply Subtype.ext
  have key := hyc g h
  show M.ρ g ((yc (h : G ⧸ F'.fixingSubgroup.comap r) : M)) - ((yc ((g : G ⧸ _) * (h : G ⧸ _)) : M.quotientToInvariants _) : M) + ((yc (g : G ⧸ _) : M.quotientToInvariants _) : M)
    = (((n • f') ((g : G ⧸ F'.fixingSubgroup.comap r), (h : G ⧸ F'.fixingSubgroup.comap r)) : M.quotientToInvariants _) : M)
  have e1 : ((g : G ⧸ F'.fixingSubgroup.comap r) * (h : G ⧸ F'.fixingSubgroup.comap r)) = ((g * h : G) : G ⧸ F'.fixingSubgroup.comap r) := rfl
  rw [e1, ← key]
  rfl

end S_groupCohomology_exists_continuousH2SrInflation_eq_of_nsmul_eq_zero
end P2MW
export P2MW.S_groupCohomology_exists_continuousH2SrInflation_eq_of_nsmul_eq_zero (solution)
