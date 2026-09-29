-- Prove2me | solution 1 for groupCohomology.finrank_eulerTerms_eq_of_iso
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/34aaab03-688f-5e09-b90a-29071468c099

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_finrank_eulerTerms_eq_of_iso

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
open CategoryTheory Module groupCohomology ExtCitation

local notation "Γ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

namespace P2mS25PSI

section generic

variable {S : Finset Nat.Primes}

lemma lcS₁_sub {X : Type*} [AddGroup X] {f f' : Γ → X} (hf : IsLevelConstantS₁ S f) (hf' : IsLevelConstantS₁ S f') :
    IsLevelConstantS₁ S (f - f') := by
  obtain ⟨F, hF, h⟩ := hf
  obtain ⟨F', hF', h'⟩ := hf'
  refine ⟨F ⊔ F', hF.sup hF', fun g s hs => ?_⟩
  simp only [Pi.sub_apply]
  rw [h g s (IntermediateField.fixingSubgroup_antitone le_sup_left hs),
    h' g s (IntermediateField.fixingSubgroup_antitone le_sup_right hs)]

lemma lcS₂_sub {X : Type*} [AddGroup X] {f f' : Γ × Γ → X} (hf : IsLevelConstantS₂ S f) (hf' : IsLevelConstantS₂ S f') :
    IsLevelConstantS₂ S (f - f') := by
  obtain ⟨F, hF, h⟩ := hf
  obtain ⟨F', hF', h'⟩ := hf'
  refine ⟨F ⊔ F', hF.sup hF', fun g g' s s' hs hs' => ?_⟩
  simp only [Pi.sub_apply]
  rw [h g g' s s' (IntermediateField.fixingSubgroup_antitone le_sup_left hs)
      (IntermediateField.fixingSubgroup_antitone le_sup_left hs'),
    h' g g' s s' (IntermediateField.fixingSubgroup_antitone le_sup_right hs)
      (IntermediateField.fixingSubgroup_antitone le_sup_right hs')]

variable {k : Type} [CommRing k] {A B : Rep.{0} k Γ} (φ : A ⟶ B)

lemma d₀₁_comp (m : A) : (d₀₁ B).hom (φ.hom m) = φ.hom ∘ (d₀₁ A).hom m := by
  funext g
  simp only [d₀₁_hom_apply, Function.comp_apply, map_sub, Rep.hom_comm_apply]

lemma d₁₂_comp (e : Γ → A) : (d₁₂ B).hom (φ.hom ∘ e) = φ.hom ∘ (d₁₂ A).hom e := by
  funext ⟨g, h⟩
  simp only [d₁₂_hom_apply, Function.comp_apply, map_add, map_sub, Rep.hom_comm_apply]

lemma d₂₃_comp (e : Γ × Γ → A) : (d₂₃ B).hom (φ.hom ∘ e) = φ.hom ∘ (d₂₃ A).hom e := by
  funext ⟨g, h, j⟩
  simp only [d₂₃_hom_apply, Function.comp_apply, map_add, map_sub, Rep.hom_comm_apply]

lemma d₁₂_d₀₁ (m : B) : (d₁₂ B).hom ((d₀₁ B).hom m) = 0 :=
  LinearMap.mem_ker.1 (coboundaries₁_le_cocycles₁ B ⟨m, rfl⟩)

lemma d₂₃_d₁₂ (y : Γ → B) : (d₂₃ B).hom ((d₁₂ B).hom y) = 0 :=
  LinearMap.mem_ker.1 (coboundaries₂_le_cocycles₂ B ⟨y, rfl⟩)

lemma d₁₂_cocycles₁ (b : cocycles₁ B) : (d₁₂ B).hom b = 0 := LinearMap.mem_ker.1 b.2

lemma d₂₃_of_mem_cocycles₂ {b : Γ × Γ → B} (hb : b ∈ cocycles₂ B) : (d₂₃ B).hom b = 0 := LinearMap.mem_ker.1 hb

lemma comp_injective (hφ : Function.Injective φ.hom) {ι : Type*} {x y : ι → A}
    (h : φ.hom ∘ x = φ.hom ∘ y) : x = y :=
  funext fun i => hφ (congrFun h i)
end generic

section H1api
variable {k : Type} [CommRing k] {A B : Rep.{0} k Γ}

lemma H1π_hom_eq_zero_iff (x : cocycles₁ A) : (H1π A).hom x = 0 ↔ (x : Γ → A) ∈ coboundaries₁ A :=
  H1π_eq_zero_iff x

lemma H1π_hom_eq_iff (x y : cocycles₁ A) : (H1π A).hom x = (H1π A).hom y ↔ (x : Γ → A) - y ∈ coboundaries₁ A :=
  H1π_eq_iff x y

lemma map_hom_H1π_hom (φ : A ⟶ B) (x : cocycles₁ A) :
    (map (MonoidHom.id Γ) φ 1).hom ((H1π A).hom x) = (H1π B).hom (mapCocycles₁ (MonoidHom.id Γ) φ x) :=
  H1π_comp_map_apply (MonoidHom.id Γ) φ x

lemma coe_mapCocycles₁_id (φ : A ⟶ B) (x : cocycles₁ A) :
    (mapCocycles₁ (MonoidHom.id Γ) φ x : Γ → B) = φ.hom ∘ (x : Γ → A) := rfl

end H1api

section functorial
variable (S : Finset Nat.Primes) {k : Type} [CommRing k] {A B : Rep.{0} k Γ} (φ : A ⟶ B)

noncomputable def mapH1S : continuousH1S S A →ₗ[k] continuousH1S S B :=
  ((map (MonoidHom.id Γ) φ 1).hom ∘ₗ (continuousH1S S A).subtype).codRestrict _ fun x => by
    obtain ⟨c, hc, hx⟩ := (mem_continuousH1S_iff S A _).1 x.2
    show (map (MonoidHom.id Γ) φ 1).hom (x : H1 A) ∈ continuousH1S S B
    rw [← hx, map_hom_H1π_hom]
    exact (mem_continuousH1S_iff S B _).2 ⟨_, by rw [coe_mapCocycles₁_id]; exact hc.comp _, rfl⟩

lemma coe_mapH1S (x : continuousH1S S A) : (mapH1S S φ x : H1 B) = (map (MonoidHom.id Γ) φ 1).hom x := rfl

lemma exists_repS (x : continuousH1S S A) : ∃ c : cocycles₁ A, IsLevelConstantS₁ S c ∧ (H1π A).hom c = x :=
  (mem_continuousH1S_iff S A _).1 x.2

noncomputable def mapZ2S : levelCocyclesS₂ S A →ₗ[k] levelCocyclesS₂ S B :=
  (φ.hom.toLinearMap.compLeft (Γ × Γ)).restrict fun z hz => by
    refine ⟨?_, hz.2.comp φ.hom⟩
    show (d₂₃ B).hom (φ.hom ∘ z) = 0
    rw [d₂₃_comp, d₂₃_of_mem_cocycles₂ hz.1]
    funext x
    exact map_zero φ.hom

lemma coe_mapZ2S (z : levelCocyclesS₂ S A) : (mapZ2S S φ z : Γ × Γ → B) = φ.hom ∘ (z : Γ × Γ → A) := rfl

noncomputable def mapH2S : continuousH2S S A →ₗ[k] continuousH2S S B :=
  Submodule.mapQ _ _ (mapZ2S S φ) fun z hz => by
    simp only [Submodule.mem_comap, Submodule.subtype_apply] at hz ⊢
    obtain ⟨x, hx, hxz⟩ := (mem_levelCoboundariesS₂_iff S A _).1 hz
    exact (mem_levelCoboundariesS₂_iff S B _).2 ⟨φ.hom ∘ x, hx.comp _, by rw [d₁₂_comp, hxz]; rfl⟩

lemma mapH2S_π (z : levelCocyclesS₂ S A) : mapH2S S φ (continuousH2Sπ S A z) = continuousH2Sπ S B (mapZ2S S φ z) :=
  rfl

lemma mapH2S_pin (z : levelCocyclesS₂ S A) (z' : levelCocyclesS₂ S B)
    (h : ∀ st, (z' : Γ × Γ → B) st = φ.hom ((z : Γ × Γ → A) st)) :
    mapH2S S φ (continuousH2Sπ S A z) = continuousH2Sπ S B z' := by
  rw [mapH2S_π]
  congr 1
  exact Subtype.ext (funext fun st => (h st).symm)

noncomputable def πS (M : Rep.{0} k Γ) : levelCocyclesS₁ S M →ₗ[k] continuousH1S S M :=
  ((H1π M).hom ∘ₗ (levelCocyclesS₁ S M).subtype).codRestrict _ fun c => Submodule.mem_map_of_mem c.2

lemma πS_surjective (M : Rep.{0} k Γ) : Function.Surjective (πS S M) := by
  rintro ⟨x, hx⟩
  obtain ⟨c, hc, rfl⟩ := (Submodule.mem_map).1 hx
  exact ⟨⟨c, hc⟩, rfl⟩

lemma coe_πS {M : Rep.{0} k Γ} (c : levelCocyclesS₁ S M) : (πS S M c : H1 M) = (H1π M).hom (c : cocycles₁ M) := rfl

end functorial

section inv
variable {k : Type} [CommRing k] {H : Type} [Group H]

def invMap {A B : Rep.{0} k H} (φ : A ⟶ B) : A.ρ.invariants →ₗ[k] B.ρ.invariants where
  toFun x := ⟨φ.hom x, fun g => by rw [← Rep.hom_comm_apply, x.2 g]⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smul _ _ _)

lemma coe_invMap {A B : Rep.{0} k H} (φ : A ⟶ B) (x : A.ρ.invariants) : (invMap φ x : B) = φ.hom x := rfl

noncomputable def invEquiv {A B : Rep.{0} k H} (e : A ≅ B) : A.ρ.invariants ≃ₗ[k] B.ρ.invariants :=
  { invMap e.hom with
    invFun := invMap e.inv
    left_inv := fun x => Subtype.ext (by
      show e.inv.hom (e.hom.hom x) = x
      have h : (e.hom ≫ e.inv).hom x = (𝟙 A : A ⟶ A).hom x := by rw [e.hom_inv_id]
      exact h)
    right_inv := fun x => Subtype.ext (by
      show e.hom.hom (e.inv.hom x) = x
      have h : (e.inv ≫ e.hom).hom x = (𝟙 B : B ⟶ B).hom x := by rw [e.inv_hom_id]
      exact h) }

end inv

end P2mS25PSI

open P2mS25PSI in
set_option maxHeartbeats 6400000 in
theorem solution
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes)
    (M N : Rep.{0} (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (e : M ≅ N) :
    finrank (ZMod p) M.ρ.invariants = finrank (ZMod p) N.ρ.invariants ∧
    finrank (ZMod p) (continuousH1S S M) = finrank (ZMod p) (continuousH1S S N) ∧
    finrank (ZMod p) (continuousH2S S M) = finrank (ZMod p) (continuousH2S S N) ∧
    finrank (ZMod p) (Rep.res (extArithLoc S (Sum.inl ())) M).ρ.invariants
      = finrank (ZMod p) (Rep.res (extArithLoc S (Sum.inl ())) N).ρ.invariants ∧
    finrank (ZMod p) M = finrank (ZMod p) N := by
  classical
  have hid : ∀ (x : M), e.inv.hom (e.hom.hom x) = x := fun x => by
    have h : (e.hom ≫ e.inv).hom x = (𝟙 M : M ⟶ M).hom x := by rw [e.hom_inv_id]
    exact h
  have hid' : ∀ (y : N), e.hom.hom (e.inv.hom y) = y := fun y => by
    have h : (e.inv ≫ e.hom).hom y = (𝟙 N : N ⟶ N).hom y := by rw [e.inv_hom_id]
    exact h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  ·
    exact (invEquiv e).finrank_eq
  ·
    have h1 : ∀ x : H1 M, (map (MonoidHom.id Γ) e.inv 1).hom ((map (MonoidHom.id Γ) e.hom 1).hom x) = x := by
      intro x
      have hc : map (MonoidHom.id Γ) e.hom 1 ≫ map (MonoidHom.id Γ) e.inv 1 = 𝟙 _ := by
        rw [← map_id_comp, e.hom_inv_id, map_id]
      exact congrArg (fun f : H1 M ⟶ H1 M => f.hom x) hc
    have h2 : ∀ y : H1 N, (map (MonoidHom.id Γ) e.hom 1).hom ((map (MonoidHom.id Γ) e.inv 1).hom y) = y := by
      intro y
      have hc : map (MonoidHom.id Γ) e.inv 1 ≫ map (MonoidHom.id Γ) e.hom 1 = 𝟙 _ := by
        rw [← map_id_comp, e.inv_hom_id, map_id]
      exact congrArg (fun f : H1 N ⟶ H1 N => f.hom y) hc
    let E : continuousH1S S M ≃ₗ[ZMod p] continuousH1S S N :=
      { mapH1S S e.hom with
        invFun := mapH1S S e.inv
        left_inv := fun x => Subtype.ext (by rw [LinearMap.toFun_eq_coe, coe_mapH1S, coe_mapH1S]; exact h1 x)
        right_inv := fun y => Subtype.ext (by rw [LinearMap.toFun_eq_coe, coe_mapH1S, coe_mapH1S]; exact h2 y) }
    exact E.finrank_eq
  ·
    have hz : ∀ z : levelCocyclesS₂ S M, mapZ2S S e.inv (mapZ2S S e.hom z) = z := fun z =>
      Subtype.ext (funext fun st => by rw [coe_mapZ2S, Function.comp_apply, coe_mapZ2S, Function.comp_apply, hid])
    have hz' : ∀ z : levelCocyclesS₂ S N, mapZ2S S e.hom (mapZ2S S e.inv z) = z := fun z =>
      Subtype.ext (funext fun st => by rw [coe_mapZ2S, Function.comp_apply, coe_mapZ2S, Function.comp_apply, hid'])
    have hsurjM : Function.Surjective (continuousH2Sπ S M) := Submodule.Quotient.mk_surjective _
    have hsurjN : Function.Surjective (continuousH2Sπ S N) := Submodule.Quotient.mk_surjective _
    let E : continuousH2S S M ≃ₗ[ZMod p] continuousH2S S N :=
      { mapH2S S e.hom with
        invFun := mapH2S S e.inv
        left_inv := fun x => by
          obtain ⟨z, rfl⟩ := hsurjM x
          show mapH2S S e.inv (mapH2S S e.hom (continuousH2Sπ S M z)) = continuousH2Sπ S M z
          rw [mapH2S_π, mapH2S_π, hz]
        right_inv := fun y => by
          obtain ⟨z, rfl⟩ := hsurjN y
          show mapH2S S e.hom (mapH2S S e.inv (continuousH2Sπ S N z)) = continuousH2Sπ S N z
          rw [mapH2S_π, mapH2S_π, hz'] }
    exact E.finrank_eq
  ·
    exact (invEquiv ((Rep.resFunctor (extArithLoc S (Sum.inl ()))).mapIso e)).finrank_eq
  ·
    let E : M ≃ₗ[ZMod p] N :=
      { e.hom.hom.toLinearMap with
        invFun := e.inv.hom
        left_inv := hid
        right_inv := hid' }
    exact E.finrank_eq

end S_groupCohomology_finrank_eulerTerms_eq_of_iso
end P2MW
export P2MW.S_groupCohomology_finrank_eulerTerms_eq_of_iso (solution)
