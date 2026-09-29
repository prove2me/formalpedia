-- Prove2me | solution 1 for groupCohomology.continuousH2SrInflation_H2pi_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/10669e1e-2506-5c16-b500-ab95e219e70f

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_LevelSubgroup
import Definitions.Def_GroupCohomology_ContinuousH2Inflation
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelInflation

import Theorems.Thm_IntermediateField_IsUnramifiedOutside_normalClosure
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_continuousH2SrInflation_H2pi_eq_zero_iff

set_option autoImplicit false
p2m_open "CategoryTheory groupCohomology P2MW.S_groupCohomology_continuousH2SrInflation_H2pi_eq_zero_iff.groupCohomology"

set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

p2m_open "CategoryTheory groupCohomology P2MW.S_groupCohomology_continuousH2SrInflation_H2pi_eq_zero_iff.groupCohomology"

noncomputable section
namespace groupCohomology
p2m_export "groupCohomology" "d₁₂ H2π cocycles₂ d₁₂_hom_apply mem_levelCoboundariesSr₂_iff continuousH2Srπ_eq_zero_iff levelInflate₁ levelInflate₁_apply levelInflate₁_mem_levelCochainsSr₁ continuousH2SrInflation continuousH2SrInflation_H2π"
p2m_open "groupCohomology"
namespace LayerA1

local instance isAlgebraicQbar : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
local instance isAlgClosureQbar : IsAlgClosure ℚ (AlgebraicClosure ℚ) := ⟨inferInstance, inferInstance⟩
local instance normalQbar : Normal ℚ (AlgebraicClosure ℚ) := IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)

local notation "Qbar" => (AlgebraicClosure ℚ)
local notation "Γ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

variable {S : Finset Nat.Primes}

lemma isUnramifiedOutside_finset_sup {ι : Type} (s : Finset ι) (F : ι → IntermediateField ℚ Qbar)
    (hF : ∀ i ∈ s, (F i).IsUnramifiedOutside S) : (s.sup F).IsUnramifiedOutside S := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using IntermediateField.isUnramifiedOutside_bot S
  | insert a s ha ih =>
    rw [Finset.sup_insert]
    exact (hF a (Finset.mem_insert_self a s)).sup (ih fun i hi => hF i (Finset.mem_insert_of_mem hi))

lemma exists_galois_level {F : IntermediateField ℚ Qbar} (hF : F.IsUnramifiedOutside S) :
    ∃ N : IntermediateField ℚ Qbar, N.IsUnramifiedOutside S ∧ IsGalois ℚ N ∧ F ≤ N := by
  haveI : FiniteDimensional ℚ ↥F := hF.1
  haveI : IsGalois ℚ Qbar := ⟨⟩
  exact ⟨IntermediateField.normalClosure ℚ (↥F) Qbar, hF.normalClosure, IsGalois.normalClosure ℚ (↥F) Qbar, IntermediateField.le_normalClosure F⟩

end LayerA1
end groupCohomology
end

noncomputable section
namespace groupCohomology
p2m_export "groupCohomology" "d₁₂ H2π cocycles₂ d₁₂_hom_apply mem_levelCoboundariesSr₂_iff continuousH2Srπ_eq_zero_iff levelInflate₁ levelInflate₁_apply levelInflate₁_mem_levelCochainsSr₁ continuousH2SrInflation continuousH2SrInflation_H2π"
p2m_open "groupCohomology"
namespace LayerA1

local instance isAlgebraicQbar'' : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
local instance isAlgClosureQbar'' : IsAlgClosure ℚ (AlgebraicClosure ℚ) := ⟨inferInstance, inferInstance⟩
local instance normalQbar'' : Normal ℚ (AlgebraicClosure ℚ) := IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)

local notation "Qbar" => (AlgebraicClosure ℚ)
local notation "Γ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

theorem main2 {k G : Type} [CommRing k] [Group G] (r : G →* Γ) (S : Finset Nat.Primes) (M : Rep.{0} k G)
    (hsm : ∀ m : M, ∃ F : IntermediateField ℚ Qbar, F.IsUnramifiedOutside S ∧ ∀ s : G, r s ∈ F.fixingSubgroup → M.ρ s m = m)
    (F : IntermediateField ℚ Qbar) (hF : F.IsUnramifiedOutside S) [Normal ℚ F]
    (f : cocycles₂ (M.quotientToInvariants (F.fixingSubgroup.comap r))) :
    continuousH2SrInflation r S M F hF (H2π _ f) = 0 ↔
    ∃ (F' : IntermediateField ℚ Qbar) (_ : F'.IsUnramifiedOutside S) (_ : IsGalois ℚ F') (_ : F ≤ F')
      (y : (G ⧸ F'.fixingSubgroup.comap r) → M.quotientToInvariants (F'.fixingSubgroup.comap r)),
      ∀ g h : G, ((f ((g : G ⧸ F.fixingSubgroup.comap r), (h : G ⧸ F.fixingSubgroup.comap r)) : M.quotientToInvariants _) : M)
        = M.ρ g (y (h : G ⧸ F'.fixingSubgroup.comap r)) - (y ((g * h : G) : G ⧸ F'.fixingSubgroup.comap r) : M) + y (g : G ⧸ F'.fixingSubgroup.comap r) := by
  classical
  haveI : FiniteDimensional ℚ ↥F := hF.1
  rw [continuousH2SrInflation_H2π, continuousH2Srπ_eq_zero_iff, mem_levelCoboundariesSr₂_iff]
  constructor
  · rintro ⟨b, ⟨Fb, hFb, hb⟩, hdb⟩

    obtain ⟨F₁, hF₁, hG₁, h1⟩ := exists_galois_level (hF.sup hFb)
    haveI : FiniteDimensional ℚ ↥F₁ := hF₁.1
    haveI : IsGalois ℚ ↥F₁ := hG₁
    set U₁ : Subgroup G := F₁.fixingSubgroup.comap r with hU₁
    haveI : Fintype (G ⧸ U₁) := Fintype.ofFinite _
    have hright : ∀ (g s : G), s ∈ U₁ → b (g * s) = b g :=
      fun g s hs => hb g s (IntermediateField.fixingSubgroup_antitone (le_sup_right.trans h1) hs)
    let Fv : M → IntermediateField ℚ Qbar := fun m => Classical.choose (hsm m)
    have hFv : ∀ m, (Fv m).IsUnramifiedOutside S ∧ ∀ s : G, r s ∈ (Fv m).fixingSubgroup → M.ρ s m = m := fun m => Classical.choose_spec (hsm m)
    let T : Finset M := Finset.image (fun q : G ⧸ U₁ => b q.out) Finset.univ
    have hT : ∀ g : G, b g ∈ T := by
      intro g
      obtain ⟨s, hs⟩ := QuotientGroup.mk_out_eq_mul U₁ g
      refine Finset.mem_image.2 ⟨(g : G ⧸ U₁), Finset.mem_univ _, ?_⟩
      change b (g : G ⧸ U₁).out = _
      rw [hs, hright g s s.2]
    set F₂ : IntermediateField ℚ Qbar := T.sup Fv with hF₂
    have hF₂S : F₂.IsUnramifiedOutside S := isUnramifiedOutside_finset_sup T Fv fun m _ => (hFv m).1
    obtain ⟨F', hF', hG', h12⟩ := exists_galois_level (hF₁.sup hF₂S)
    haveI : FiniteDimensional ℚ ↥F' := hF'.1
    set U : Subgroup G := F'.fixingSubgroup.comap r with hU
    have hUU₁ : U ≤ U₁ := fun s hs => IntermediateField.fixingSubgroup_antitone (le_sup_left.trans h12) hs
    have hfix : ∀ (g s : G), s ∈ U → M.ρ s (b g) = b g := by
      intro g s hs
      apply (hFv _).2 s
      exact IntermediateField.fixingSubgroup_antitone ((Finset.le_sup (f := Fv) (hT g)).trans (le_sup_right.trans h12)) hs
    let y : (G ⧸ U) → M.quotientToInvariants U := fun q => ⟨b q.out, fun s => hfix _ s s.2⟩
    have hy_coe : ∀ g : G, ((y (g : G ⧸ U) : M.quotientToInvariants U) : M) = b g := by
      intro g
      obtain ⟨s, hs⟩ := QuotientGroup.mk_out_eq_mul U g
      change b (g : G ⧸ U).out = _
      rw [hs, hright g s (hUU₁ s.2)]
    refine ⟨F', hF', hG', (le_sup_left.trans h1).trans (le_sup_left.trans h12), y, fun g h => ?_⟩
    rw [hy_coe, hy_coe, hy_coe]
    have := congrFun hdb (g, h)
    rw [d₁₂_hom_apply] at this
    rw [this]
    rfl
  · rintro ⟨F', hF', hG', hFF', y, hy⟩
    haveI : FiniteDimensional ℚ ↥F' := hF'.1
    refine ⟨levelInflate₁ r M F' y, levelInflate₁_mem_levelCochainsSr₁ r S M F' hF' y, ?_⟩
    funext gh
    obtain ⟨g, h⟩ := gh
    rw [d₁₂_hom_apply, levelInflate₁_apply, levelInflate₁_apply, levelInflate₁_apply]
    exact (hy g h).symm

end LayerA1
end groupCohomology
end

open _root_.groupCohomology _root_.P2MW.S_groupCohomology_continuousH2SrInflation_H2pi_eq_zero_iff.groupCohomology in
theorem solution
    {k G : Type} [CommRing k] [Group G] (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (S : Finset Nat.Primes) (M : Rep.{0} k G)
    (hsm : ∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧ ∀ s : G, r s ∈ F.fixingSubgroup → M.ρ s m = m)
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hF : F.IsUnramifiedOutside S) [Normal ℚ F]
    (f : cocycles₂ (M.quotientToInvariants (F.fixingSubgroup.comap r))) :
    continuousH2SrInflation r S M F hF (H2π _ f) = 0 ↔
    ∃ (F' : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : F'.IsUnramifiedOutside S) (_ : IsGalois ℚ F') (_ : F ≤ F')
      (y : (G ⧸ F'.fixingSubgroup.comap r) → M.quotientToInvariants (F'.fixingSubgroup.comap r)),
      ∀ g h : G, ((f ((g : G ⧸ F.fixingSubgroup.comap r), (h : G ⧸ F.fixingSubgroup.comap r)) : M.quotientToInvariants _) : M)
        = M.ρ g (y (h : G ⧸ F'.fixingSubgroup.comap r)) - (y ((g * h : G) : G ⧸ F'.fixingSubgroup.comap r) : M) + y (g : G ⧸ F'.fixingSubgroup.comap r) :=
  LayerA1.main2 r S M hsm F hF f

end S_groupCohomology_continuousH2SrInflation_H2pi_eq_zero_iff
end P2MW
export P2MW.S_groupCohomology_continuousH2SrInflation_H2pi_eq_zero_iff (solution)
