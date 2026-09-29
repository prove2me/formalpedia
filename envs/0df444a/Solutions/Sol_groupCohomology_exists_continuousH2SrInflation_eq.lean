-- Prove2me | solution 1 for groupCohomology.exists_continuousH2SrInflation_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/5a1ba9dc-8b68-572b-b79a-93c6be4ab043

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

namespace P2MW.S_groupCohomology_exists_continuousH2SrInflation_eq

set_option autoImplicit false
p2m_open "CategoryTheory groupCohomology P2MW.S_groupCohomology_exists_continuousH2SrInflation_eq.groupCohomology"

set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

p2m_open "CategoryTheory groupCohomology P2MW.S_groupCohomology_exists_continuousH2SrInflation_eq.groupCohomology"

noncomputable section
namespace groupCohomology
p2m_export "groupCohomology" "H2 H2π congr cocycles₂ mem_cocycles₂_iff continuousH2Sr continuousH2Srπ_surjective levelInflate₂_apply coe_levelInflateCocyclesSr₂ continuousH2SrInflation continuousH2SrInflation_H2π"
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
p2m_export "groupCohomology" "H2 H2π congr cocycles₂ mem_cocycles₂_iff continuousH2Sr continuousH2Srπ_surjective levelInflate₂_apply coe_levelInflateCocyclesSr₂ continuousH2SrInflation continuousH2SrInflation_H2π"
p2m_open "groupCohomology"
namespace LayerA1

local instance isAlgebraicQbar' : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
local instance isAlgClosureQbar' : IsAlgClosure ℚ (AlgebraicClosure ℚ) := ⟨inferInstance, inferInstance⟩
local instance normalQbar' : Normal ℚ (AlgebraicClosure ℚ) := IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)

local notation "Qbar" => (AlgebraicClosure ℚ)
local notation "Γ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

theorem main {k G : Type} [CommRing k] [Group G] (r : G →* Γ) (S : Finset Nat.Primes) (M : Rep.{0} k G)
    (hsm : ∀ m : M, ∃ F : IntermediateField ℚ Qbar, F.IsUnramifiedOutside S ∧ ∀ s : G, r s ∈ F.fixingSubgroup → M.ρ s m = m)
    (z : continuousH2Sr r S M) :
    ∃ (F : IntermediateField ℚ Qbar) (hF : F.IsUnramifiedOutside S) (_ : IsGalois ℚ F)
      (y : H2 (M.quotientToInvariants (F.fixingSubgroup.comap r))),
      continuousH2SrInflation r S M F hF y = z := by
  classical
  obtain ⟨w, rfl⟩ := continuousH2Srπ_surjective r S M z
  obtain ⟨hwc, F₀, hF₀, hw₀⟩ := w.2

  obtain ⟨F₁, hF₁, hG₁, h01⟩ := exists_galois_level hF₀
  haveI : FiniteDimensional ℚ ↥F₁ := hF₁.1
  haveI : IsGalois ℚ ↥F₁ := hG₁
  set U₁ : Subgroup G := F₁.fixingSubgroup.comap r with hU₁
  haveI : Fintype (G ⧸ U₁) := Fintype.ofFinite _
  have hright : ∀ (g g' s s' : G), s ∈ U₁ → s' ∈ U₁ → (w : G × G → M) (g * s, g' * s') = (w : G × G → M) (g, g') :=
    fun g g' s s' hs hs' => hw₀ g g' s s' (IntermediateField.fixingSubgroup_antitone h01 hs) (IntermediateField.fixingSubgroup_antitone h01 hs')

  let Fv : M → IntermediateField ℚ Qbar := fun m => Classical.choose (hsm m)
  have hFv : ∀ m, (Fv m).IsUnramifiedOutside S ∧ ∀ s : G, r s ∈ (Fv m).fixingSubgroup → M.ρ s m = m := fun m => Classical.choose_spec (hsm m)
  let T : Finset M := Finset.image (fun qq : (G ⧸ U₁) × (G ⧸ U₁) => (w : G × G → M) (qq.1.out, qq.2.out)) Finset.univ
  have hT : ∀ g g' : G, (w : G × G → M) (g, g') ∈ T := by
    intro g g'
    obtain ⟨s, hs⟩ := QuotientGroup.mk_out_eq_mul U₁ g
    obtain ⟨s', hs'⟩ := QuotientGroup.mk_out_eq_mul U₁ g'
    refine Finset.mem_image.2 ⟨((g : G ⧸ U₁), (g' : G ⧸ U₁)), Finset.mem_univ _, ?_⟩
    change (w : G × G → M) ((g : G ⧸ U₁).out, (g' : G ⧸ U₁).out) = _
    rw [hs, hs', hright g g' s s' s.2 s'.2]
  set F₂ : IntermediateField ℚ Qbar := T.sup Fv with hF₂
  have hF₂S : F₂.IsUnramifiedOutside S := isUnramifiedOutside_finset_sup T Fv fun m _ => (hFv m).1

  obtain ⟨F, hF, hG, h12F⟩ := exists_galois_level (hF₁.sup hF₂S)
  haveI : FiniteDimensional ℚ ↥F := hF.1
  set U : Subgroup G := F.fixingSubgroup.comap r with hU
  have hUU₁ : U ≤ U₁ := fun s hs => IntermediateField.fixingSubgroup_antitone (le_sup_left.trans h12F) hs
  have hfix : ∀ (g g' : G) (s : G), s ∈ U → M.ρ s ((w : G × G → M) (g, g')) = (w : G × G → M) (g, g') := by
    intro g g' s hs
    apply (hFv _).2 s
    have hle : Fv ((w : G × G → M) (g, g')) ≤ F := (Finset.le_sup (f := Fv) (hT g g')).trans (le_sup_right.trans h12F)
    exact IntermediateField.fixingSubgroup_antitone hle hs
  have hrightU : ∀ (g g' s s' : G), s ∈ U → s' ∈ U → (w : G × G → M) (g * s, g' * s') = (w : G × G → M) (g, g') :=
    fun g g' s s' hs hs' => hright g g' s s' (hUU₁ hs) (hUU₁ hs')

  let yfun : (G ⧸ U) × (G ⧸ U) → M.quotientToInvariants U := fun qq =>
    ⟨(w : G × G → M) (qq.1.out, qq.2.out), fun s => hfix _ _ s s.2⟩
  have hy_coe : ∀ g h : G, ((yfun ((g : G ⧸ U), (h : G ⧸ U)) : M.quotientToInvariants U) : M) = (w : G × G → M) (g, h) := by
    intro g h
    obtain ⟨s, hs⟩ := QuotientGroup.mk_out_eq_mul U g
    obtain ⟨s', hs'⟩ := QuotientGroup.mk_out_eq_mul U h
    change (w : G × G → M) ((g : G ⧸ U).out, (h : G ⧸ U).out) = _
    rw [hs, hs', hrightU g h s s' s.2 s'.2]
  have hy : yfun ∈ cocycles₂ (M.quotientToInvariants U) := by
    rw [mem_cocycles₂_iff]
    intro q₁ q₂ q₃
    induction q₁ using QuotientGroup.induction_on with | H g₁ =>
    induction q₂ using QuotientGroup.induction_on with | H g₂ =>
    induction q₃ using QuotientGroup.induction_on with | H g₃ =>
    apply Subtype.ext
    change ((yfun (((g₁ * g₂ : G) : G ⧸ U), (g₃ : G ⧸ U)) : M.quotientToInvariants U) : M) + (yfun ((g₁ : G ⧸ U), (g₂ : G ⧸ U)) : M) =
      M.ρ g₁ ((yfun ((g₂ : G ⧸ U), (g₃ : G ⧸ U)) : M.quotientToInvariants U) : M) + (yfun ((g₁ : G ⧸ U), ((g₂ * g₃ : G) : G ⧸ U)) : M)
    rw [hy_coe, hy_coe, hy_coe, hy_coe]
    exact (mem_cocycles₂_iff _).1 hwc g₁ g₂ g₃
  refine ⟨F, hF, hG, H2π _ ⟨yfun, hy⟩, ?_⟩
  rw [continuousH2SrInflation_H2π]
  congr 1
  apply Subtype.ext
  funext gh
  obtain ⟨g, h⟩ := gh
  rw [coe_levelInflateCocyclesSr₂, levelInflate₂_apply]
  exact hy_coe g h

end LayerA1
end groupCohomology
end

open _root_.groupCohomology _root_.P2MW.S_groupCohomology_exists_continuousH2SrInflation_eq.groupCohomology in
theorem solution
    {k G : Type} [CommRing k] [Group G] (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (S : Finset Nat.Primes) (M : Rep.{0} k G)
    (hsm : ∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧ ∀ s : G, r s ∈ F.fixingSubgroup → M.ρ s m = m)
    (z : continuousH2Sr r S M) :
    ∃ (F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hF : F.IsUnramifiedOutside S) (_ : IsGalois ℚ F)
      (y : H2 (M.quotientToInvariants (F.fixingSubgroup.comap r))),
      continuousH2SrInflation r S M F hF y = z :=
  LayerA1.main r S M hsm z

end S_groupCohomology_exists_continuousH2SrInflation_eq
end P2MW
export P2MW.S_groupCohomology_exists_continuousH2SrInflation_eq (solution)
