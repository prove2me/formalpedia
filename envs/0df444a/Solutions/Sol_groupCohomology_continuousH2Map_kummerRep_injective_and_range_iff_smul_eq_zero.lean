-- Prove2me | solution 1 for groupCohomology.continuousH2Map_kummerRep_injective_and_range_iff_smul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/5ae62b9d-1c6a-5494-92b8-28115899b7e7

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_ContinuousH2Map
import Definitions.Def_GroupCohomology_ContinuousH1
import Definitions.Def_GroupCohomology_Kummer
import Theorems.Thm_groupCohomology_deltaCochain0_mem_cocycles1_and_isLevelConstant1
import Theorems.Thm_groupCohomology_deltaCochain0_mem_coboundaries1_iff
import Theorems.Thm_groupCohomology_comp_mem_coboundaries1_iff_exists_invariants_sub_deltaCochain0
import Theorems.Thm_groupCohomology_comp_mem_coboundaries1_iff_exists_isLevelConstant1_sub_comp
import Theorems.Thm_groupCohomology_deltaCochain1_mem_levelCoboundaries2_iff
import Theorems.Thm_groupCohomology_comp_mem_levelCoboundaries2_iff_exists_sub_deltaCochain1
import Theorems.Thm_groupCohomology_comp_mem_levelCoboundaries2_iff_exists_levelCocycles2_sub_comp
import Theorems.Thm_groupCohomology_preimageFun_comp_d12_sub_deltaCochain1_mem_levelCoboundaries2
import Theorems.Thm_groupCohomology_exists_linearMap_levelCocycles1_continuousH2_eq_continuousH2pi_deltaCochain1
import Theorems.Thm_IntermediateField_exists_forall_mem_fixingSubgroup_smul_eq_of_cofinal
import Theorems.Thm_groupCohomology_isMulCoboundary1_of_isMulCocycle1_of_level
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_continuousH2Map_kummerRep_injective_and_range_iff_smul_eq_zero

set_option autoImplicit false
set_option maxHeartbeats 1600000

universe u

open CategoryTheory

namespace P2mS26EP
open groupCohomology

variable {k G : Type u} [CommRing k] [Group G]
  {r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)} {A B C : Rep.{u} k G}

lemma H1π_hom_eq_zero_iff (x : cocycles₁ A) : (H1π A).hom x = 0 ↔ (x : G → A) ∈ coboundaries₁ A :=
  H1π_eq_zero_iff x

lemma H1π_hom_eq_iff (x y : cocycles₁ A) : (H1π A).hom x = (H1π A).hom y ↔ (x : G → A) - y ∈ coboundaries₁ A :=
  H1π_eq_iff x y

lemma map_hom_H1π_hom (φ : A ⟶ B) (x : cocycles₁ A) :
    (map (MonoidHom.id G) φ 1).hom ((H1π A).hom x) = (H1π B).hom (mapCocycles₁ (MonoidHom.id G) φ x) :=
  H1π_comp_map_apply (MonoidHom.id G) φ x

lemma coe_mapCocycles₁_id (φ : A ⟶ B) (x : cocycles₁ A) :
    (mapCocycles₁ (MonoidHom.id G) φ x : G → B) = φ.hom ∘ (x : G → A) := rfl

noncomputable def inv₀ (φ : A ⟶ B) : A.ρ.invariants →ₗ[k] B.ρ.invariants :=
  (φ.hom.toLinearMap ∘ₗ A.ρ.invariants.subtype).codRestrict _ fun a g => by
    show B.ρ g (φ.hom (a : A)) = φ.hom (a : A)
    rw [← Rep.hom_comm_apply, a.2 g]

lemma coe_inv₀ (φ : A ⟶ B) (a : A.ρ.invariants) : (inv₀ φ a : B) = φ.hom a := rfl

lemma inv₀_injective (φ : A ⟶ B) (hφ : Function.Injective φ.hom) : Function.Injective (inv₀ φ) :=
  fun a b h => Subtype.ext (hφ (by simpa only [coe_inv₀] using congrArg Subtype.val h))

lemma exact_inv₀ (φ : A ⟶ B) (ψ : B ⟶ C) (hφ : Function.Injective φ.hom)
    (hex : ∀ b : B, ψ.hom b = 0 ↔ ∃ a : A, φ.hom a = b) :
    Function.Exact (inv₀ φ) (inv₀ ψ) := by
  intro b
  constructor
  · intro hb
    have hb' : ψ.hom (b : B) = 0 := by have h__af := congrArg Subtype.val hb; simp only [coe_inv₀] at h__af; exact h__af
    obtain ⟨a, ha⟩ := (hex _).1 hb'
    refine ⟨⟨a, fun g => hφ ?_⟩, Subtype.ext (by simpa only [coe_inv₀] using ha)⟩
    rw [Rep.hom_comm_apply, ha]; exact b.2 g
  · rintro ⟨a, rfl⟩
    apply Subtype.ext
    have h__af := ((hex _).2 ⟨(a : A), rfl⟩)
    simp only [coe_inv₀] at h__af ⊢
    exact h__af

section delta0

variable (φ : A ⟶ B) (ψ : B ⟶ C) (hφ : Function.Injective φ.hom) (hψ : Function.Surjective ψ.hom)
  (hex : ∀ b : B, ψ.hom b = 0 ↔ ∃ a : A, φ.hom a = b)
  (hsm : ∀ m : B, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s, r s ∈ F.fixingSubgroup → B.ρ s m = m)

lemma ker_lift {c : C} (hc : c ∈ C.ρ.invariants) {b : B} (hb : ψ.hom b = c) (g : G) :
    ψ.hom (B.ρ g b - b) = 0 := by
  rw [map_sub, Rep.hom_comm_apply, hb, sub_eq_zero]; exact hc g

include hex in
lemma φ_delta0 {c : C} (hc : c ∈ C.ρ.invariants) (g : G) :
    φ.hom (deltaCochain₀ φ ψ hψ c g) = B.ρ g (Function.surjInv hψ c) - Function.surjInv hψ c := by
  rw [deltaCochain₀_apply]
  exact apply_preimageFun φ ((hex _).1 (ker_lift ψ hc (Function.surjInv_eq hψ c) g))

include hφ hex in

lemma delta0_sub_lift_mem {c : C} (hc : c ∈ C.ρ.invariants) (b : B) (hb : ψ.hom b = c) :
    (deltaCochain₀ φ ψ hψ c - fun g => preimageFun φ (B.ρ g b - b)) ∈ coboundaries₁ A := by
  obtain ⟨a₀, ha₀⟩ := (hex (Function.surjInv hψ c - b)).1
    (by rw [map_sub, Function.surjInv_eq hψ, hb, sub_self])
  refine ⟨a₀, funext fun g => hφ ?_⟩
  have lhs : φ.hom ((d₀₁ A).hom a₀ g) = B.ρ g (Function.surjInv hψ c - b) - (Function.surjInv hψ c - b) := by
    rw [d₀₁_hom_apply, map_sub, Rep.hom_comm_apply, ha₀]
  have rhs : φ.hom ((deltaCochain₀ φ ψ hψ c - fun g => preimageFun φ (B.ρ g b - b)) g)
      = (B.ρ g (Function.surjInv hψ c) - Function.surjInv hψ c) - (B.ρ g b - b) := by
    rw [Pi.sub_apply, map_sub, φ_delta0 φ ψ hψ hex hc, apply_preimageFun φ ((hex _).1 (ker_lift ψ hc hb g))]
  rw [lhs, rhs, map_sub]
  abel

include hφ hex hsm in
variable (r) in

noncomputable def delta₀ : C.ρ.invariants →ₗ[k] continuousH1 r A where
  toFun c := ⟨(H1π A).hom ⟨deltaCochain₀ φ ψ hψ c,
      (groupCohomology.deltaCochain0_mem_cocycles1_and_isLevelConstant1 r φ ψ hφ hψ hex hsm c c.2).1⟩,
    H1π_mem_continuousH1 r A
      (groupCohomology.deltaCochain0_mem_cocycles1_and_isLevelConstant1 r φ ψ hφ hψ hex hsm c c.2).2⟩
  map_add' c c' := by
    apply Subtype.ext
    simp only [Submodule.coe_add]
    rw [← map_add, H1π_hom_eq_iff]
    have hcc' : (c : C) + c' ∈ C.ρ.invariants := add_mem c.2 c'.2
    have hlift : ψ.hom (Function.surjInv hψ c + Function.surjInv hψ c') = (c : C) + c' := by
      rw [map_add, Function.surjInv_eq hψ, Function.surjInv_eq hψ]
    have key := delta0_sub_lift_mem φ ψ hφ hψ hex hcc' _ hlift
    have e : (fun g => preimageFun φ (B.ρ g (Function.surjInv hψ c + Function.surjInv hψ c')
        - (Function.surjInv hψ c + Function.surjInv hψ c')))
        = deltaCochain₀ φ ψ hψ c + deltaCochain₀ φ ψ hψ c' := by
      funext g
      apply hφ
      rw [apply_preimageFun φ ((hex _).1 (ker_lift ψ hcc' hlift g)), Pi.add_apply, map_add (B.ρ g),
        map_add φ.hom, φ_delta0 φ ψ hψ hex c.2, φ_delta0 φ ψ hψ hex c'.2]
      abel
    rw [e] at key
    exact key
  map_smul' t c := by
    apply Subtype.ext
    simp only [Submodule.coe_smul, RingHom.id_apply]
    rw [← map_smul, H1π_hom_eq_iff]
    have htc : t • (c : C) ∈ C.ρ.invariants := Submodule.smul_mem _ t c.2
    have hlift : ψ.hom (t • Function.surjInv hψ c) = t • (c : C) := by
      rw [map_smul, Function.surjInv_eq hψ]
    have key := delta0_sub_lift_mem φ ψ hφ hψ hex htc _ hlift
    have e : (fun g => preimageFun φ (B.ρ g (t • Function.surjInv hψ c) - t • Function.surjInv hψ c))
        = t • deltaCochain₀ φ ψ hψ c := by
      funext g
      apply hφ
      rw [apply_preimageFun φ ((hex _).1 (ker_lift ψ htc hlift g)), Pi.smul_apply, map_smul (B.ρ g),
        map_smul φ.hom, φ_delta0 φ ψ hψ hex c.2, smul_sub]
    rw [e] at key
    exact key

include hφ hex hsm in
lemma coe_delta₀ (c : C.ρ.invariants) :
    (delta₀ r φ ψ hφ hψ hex hsm c : H1 A) = (H1π A).hom ⟨deltaCochain₀ φ ψ hψ c,
      (groupCohomology.deltaCochain0_mem_cocycles1_and_isLevelConstant1 r φ ψ hφ hψ hex hsm c c.2).1⟩ := rfl

include hφ hex hsm in

lemma exact_delta₀ : Function.Exact (inv₀ ψ) (delta₀ r φ ψ hφ hψ hex hsm) := by
  intro c
  rw [← Submodule.coe_eq_zero, coe_delta₀, H1π_hom_eq_zero_iff, cocycles₁.coe_mk,
    groupCohomology.deltaCochain0_mem_coboundaries1_iff φ ψ hφ hψ hex c c.2]
  constructor
  · rintro ⟨b, hb, hbc⟩; exact ⟨⟨b, hb⟩, Subtype.ext hbc⟩
  · rintro ⟨b, hb⟩; exact ⟨b, b.2, congrArg Subtype.val hb⟩

end delta0

variable (r) in

noncomputable def mapH1 (φ : A ⟶ B) : continuousH1 r A →ₗ[k] continuousH1 r B :=
  ((map (MonoidHom.id G) φ 1).hom ∘ₗ (continuousH1 r A).subtype).codRestrict _ fun x => by
    obtain ⟨c, hc, hx⟩ := (mem_continuousH1_iff r A _).1 x.2
    show (map (MonoidHom.id G) φ 1).hom (x : H1 A) ∈ continuousH1 r B
    rw [← hx, map_hom_H1π_hom]
    exact H1π_mem_continuousH1 r B (by rw [coe_mapCocycles₁_id]; exact hc.comp _)

lemma coe_mapH1 (φ : A ⟶ B) (x : continuousH1 r A) :
    (mapH1 r φ x : H1 B) = (map (MonoidHom.id G) φ 1).hom x := rfl

lemma exists_rep (x : continuousH1 r A) :
    ∃ c : cocycles₁ A, IsLevelConstant₁ r c ∧ (H1π A).hom c = x :=
  (mem_continuousH1_iff r A _).1 x.2

section exact34

variable (φ : A ⟶ B) (ψ : B ⟶ C) (hφ : Function.Injective φ.hom) (hψ : Function.Surjective ψ.hom)
  (hex : ∀ b : B, ψ.hom b = 0 ↔ ∃ a : A, φ.hom a = b)
  (hsm : ∀ m : B, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s, r s ∈ F.fixingSubgroup → B.ρ s m = m)
include hφ hψ hex hsm

lemma exact_mapH1_A : Function.Exact (delta₀ r φ ψ hφ hψ hex hsm) (mapH1 r φ) := by
  intro x
  obtain ⟨a, ha, hax⟩ := exists_rep x
  rw [← Submodule.coe_eq_zero, coe_mapH1, ← hax, map_hom_H1π_hom, H1π_hom_eq_zero_iff, coe_mapCocycles₁_id,
    groupCohomology.comp_mem_coboundaries1_iff_exists_invariants_sub_deltaCochain0 φ ψ hφ hψ hex a]
  constructor
  · rintro ⟨c, hc, hac⟩
    refine ⟨⟨c, hc⟩, Subtype.ext ?_⟩
    rw [coe_delta₀, ← hax, H1π_hom_eq_iff]
    simpa only [cocycles₁.coe_mk, neg_sub] using neg_mem hac
  · rintro ⟨c, hcx⟩
    refine ⟨c, c.2, ?_⟩
    have := congrArg Subtype.val hcx
    rw [coe_delta₀, ← hax, H1π_hom_eq_iff, cocycles₁.coe_mk] at this
    simpa only [neg_sub] using neg_mem this

lemma exact_mapH1_B : Function.Exact (mapH1 r φ) (mapH1 r ψ) := by
  intro x
  obtain ⟨b, hb, hbx⟩ := exists_rep x
  rw [← Submodule.coe_eq_zero, coe_mapH1, ← hbx, map_hom_H1π_hom, H1π_hom_eq_zero_iff, coe_mapCocycles₁_id,
    groupCohomology.comp_mem_coboundaries1_iff_exists_isLevelConstant1_sub_comp r φ ψ hφ hψ hex hsm b hb]
  constructor
  · rintro ⟨a, ha, hab⟩
    refine ⟨⟨(H1π A).hom a, H1π_mem_continuousH1 r A ha⟩, Subtype.ext ?_⟩
    rw [coe_mapH1, Submodule.coe_mk, map_hom_H1π_hom, ← hbx, H1π_hom_eq_iff, coe_mapCocycles₁_id]
    simpa only [neg_sub] using neg_mem hab
  · rintro ⟨y, hyx⟩
    obtain ⟨a, ha, hay⟩ := exists_rep y
    refine ⟨a, ha, ?_⟩
    have := congrArg Subtype.val hyx
    rw [coe_mapH1, ← hay, map_hom_H1π_hom, ← hbx, H1π_hom_eq_iff, coe_mapCocycles₁_id] at this
    simpa only [neg_sub] using neg_mem this

end exact34

variable (r) in

noncomputable def πlc (M : Rep.{u} k G) : levelCocycles₁ r M →ₗ[k] continuousH1 r M :=
  ((H1π M).hom ∘ₗ (levelCocycles₁ r M).subtype).codRestrict _ fun c =>
    Submodule.mem_map_of_mem c.2

lemma πlc_surjective (M : Rep.{u} k G) : Function.Surjective (πlc r M) := by
  rintro ⟨x, hx⟩
  obtain ⟨c, hc, rfl⟩ := (Submodule.mem_map).1 hx
  exact ⟨⟨c, hc⟩, rfl⟩

lemma coe_πlc {M : Rep.{u} k G} (c : levelCocycles₁ r M) : (πlc r M c : H1 M) = (H1π M).hom (c : cocycles₁ M) := rfl

section delta1

variable (φ : A ⟶ B) (ψ : B ⟶ C) (hφ : Function.Injective φ.hom) (hψ : Function.Surjective ψ.hom)
  (hex : ∀ b : B, ψ.hom b = 0 ↔ ∃ a : A, φ.hom a = b)
  (hsm : ∀ m : B, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s, r s ∈ F.fixingSubgroup → B.ρ s m = m)

include hφ hex hsm in

noncomputable def δlc : levelCocycles₁ r C →ₗ[k] continuousH2 r A :=
  (groupCohomology.exists_linearMap_levelCocycles1_continuousH2_eq_continuousH2pi_deltaCochain1
    r φ ψ hφ hψ hex hsm).choose

include hφ hex hsm in
lemma δlc_spec (c : levelCocycles₁ r C) :
    ∃ h : deltaCochain₁ φ ψ hψ ((c : cocycles₁ C) : G → C) ∈ levelCocycles₂ r A,
      δlc φ ψ hφ hψ hex hsm c = continuousH2π r A ⟨_, h⟩ :=
  (groupCohomology.exists_linearMap_levelCocycles1_continuousH2_eq_continuousH2pi_deltaCochain1
    r φ ψ hφ hψ hex hsm).choose_spec c

include hφ hex hsm in
lemma δlc_eq_zero_iff (c : levelCocycles₁ r C) :
    δlc φ ψ hφ hψ hex hsm c = 0 ↔ deltaCochain₁ φ ψ hψ ((c : cocycles₁ C) : G → C) ∈ levelCoboundaries₂ r A := by
  obtain ⟨h, e⟩ := δlc_spec φ ψ hφ hψ hex hsm c
  rw [e, continuousH2π_eq_zero_iff]

include hφ hex hsm in

lemma δlc_eq_zero_of_πlc_eq_zero (c : levelCocycles₁ r C) (hc : πlc r C c = 0) :
    δlc φ ψ hφ hψ hex hsm c = 0 := by
  rw [δlc_eq_zero_iff]
  have hc' : ((c : cocycles₁ C) : G → C) ∈ coboundaries₁ C := by
    rw [← H1π_hom_eq_zero_iff, ← coe_πlc, hc, Submodule.coe_zero]
  obtain ⟨m, hm⟩ := hc'
  have hL : IsLevelConstant₁ r ((d₀₁ B).hom (Function.surjInv hψ m)) := by
    obtain ⟨F, hF, h⟩ := hsm (Function.surjInv hψ m)
    refine ⟨F, hF, fun g s hs => ?_⟩
    rw [d₀₁_hom_apply, d₀₁_hom_apply, map_mul, Module.End.mul_apply, h s hs]
  have hLc : ∀ g, ψ.hom ((d₀₁ B).hom (Function.surjInv hψ m) g) = ((c : cocycles₁ C) : G → C) g := by
    intro g
    rw [d₀₁_hom_apply, map_sub, Rep.hom_comm_apply, Function.surjInv_eq hψ, ← hm, d₀₁_hom_apply]
  have key := groupCohomology.preimageFun_comp_d12_sub_deltaCochain1_mem_levelCoboundaries2 r φ ψ hφ hψ hex
    (c : cocycles₁ C) c.2 _ hL hLc
  have hzero : preimageFun φ ∘ (d₁₂ B).hom ((d₀₁ B).hom (Function.surjInv hψ m)) = 0 := by
    have : (d₁₂ B).hom ((d₀₁ B).hom (Function.surjInv hψ m)) = 0 :=
      LinearMap.mem_ker.1 (coboundaries₁_le_cocycles₁ B ⟨_, rfl⟩)
    rw [this]
    funext p
    show preimageFun φ 0 = 0
    have := preimageFun_apply φ hφ 0
    rwa [map_zero] at this
  rw [hzero, zero_sub] at key
  simpa using neg_mem key

include hφ hex hsm in

noncomputable def delta₁Fun (y : continuousH1 r C) : continuousH2 r A :=
  δlc φ ψ hφ hψ hex hsm (πlc_surjective C y).choose

include hφ hex hsm in
lemma delta₁Fun_πlc (c : levelCocycles₁ r C) :
    delta₁Fun φ ψ hφ hψ hex hsm (πlc r C c) = δlc φ ψ hφ hψ hex hsm c := by
  have h := (πlc_surjective C (πlc r C c)).choose_spec
  rw [delta₁Fun, ← sub_eq_zero, ← map_sub]
  exact δlc_eq_zero_of_πlc_eq_zero φ ψ hφ hψ hex hsm _ (by rw [map_sub, h, sub_self])

include hφ hex hsm in
variable (r) in

noncomputable def delta₁ : continuousH1 r C →ₗ[k] continuousH2 r A where
  toFun := delta₁Fun φ ψ hφ hψ hex hsm
  map_add' y y' := by
    obtain ⟨c, rfl⟩ := πlc_surjective C y
    obtain ⟨c', rfl⟩ := πlc_surjective C y'
    rw [← map_add, delta₁Fun_πlc, delta₁Fun_πlc, delta₁Fun_πlc, map_add]
  map_smul' t y := by
    obtain ⟨c, rfl⟩ := πlc_surjective C y
    rw [← map_smul, delta₁Fun_πlc, delta₁Fun_πlc, map_smul, RingHom.id_apply]

include hφ hex hsm in
lemma delta₁_πlc (c : levelCocycles₁ r C) : delta₁ r φ ψ hφ hψ hex hsm (πlc r C c) = δlc φ ψ hφ hψ hex hsm c :=
  delta₁Fun_πlc φ ψ hφ hψ hex hsm c

include hφ hex hsm in

lemma exact_delta₁ : Function.Exact (mapH1 r ψ) (delta₁ r φ ψ hφ hψ hex hsm) := by
  intro y
  obtain ⟨c, rfl⟩ := πlc_surjective C y
  rw [delta₁_πlc, δlc_eq_zero_iff,
    groupCohomology.deltaCochain1_mem_levelCoboundaries2_iff r φ ψ hφ hψ hex hsm (c : cocycles₁ C) c.2]
  constructor
  · rintro ⟨b, hb, hcb⟩
    refine ⟨⟨(H1π B).hom b, H1π_mem_continuousH1 r B hb⟩, Subtype.ext ?_⟩
    rw [coe_mapH1, Submodule.coe_mk, map_hom_H1π_hom, coe_πlc, H1π_hom_eq_iff, coe_mapCocycles₁_id]
    simpa only [neg_sub] using neg_mem hcb
  · rintro ⟨y, hy⟩
    obtain ⟨b, hb, hby⟩ := exists_rep y
    refine ⟨b, hb, ?_⟩
    have := congrArg Subtype.val hy
    rw [coe_mapH1, ← hby, map_hom_H1π_hom, coe_πlc, H1π_hom_eq_iff, coe_mapCocycles₁_id] at this
    simpa only [neg_sub] using neg_mem this

lemma coe_levelCocycles₂Map_id (x : levelCocycles₂ r A) :
    (levelCocycles₂Map (MonoidHom.id G) (fun _ => rfl) φ.hom.toLinearMap (fun g a => Rep.hom_comm_apply φ g a) x
      : G × G → B) = φ.hom ∘ (x : G × G → A) :=
  funext fun _ => rfl

lemma continuousH2MapHom_π (x : levelCocycles₂ r A) :
    continuousH2MapHom r φ (continuousH2π r A x)
      = continuousH2π r B (levelCocycles₂Map (MonoidHom.id G) (fun _ => rfl) φ.hom.toLinearMap
          (fun g a => Rep.hom_comm_apply φ g a) x) := rfl

include hφ hex hsm in

lemma exact_H2_A : Function.Exact (delta₁ r φ ψ hφ hψ hex hsm) (continuousH2MapHom r φ) := by
  intro z
  induction z using Submodule.Quotient.induction_on with | _ x =>
  show continuousH2MapHom r φ (continuousH2π r A x) = 0 ↔ _
  rw [continuousH2MapHom_π, continuousH2π_eq_zero_iff, coe_levelCocycles₂Map_id,
    groupCohomology.comp_mem_levelCoboundaries2_iff_exists_sub_deltaCochain1 r φ ψ hφ hψ hex (x : G × G → A)]
  constructor
  · rintro ⟨c, hc, hxc⟩
    refine ⟨πlc r C ⟨c, hc⟩, ?_⟩
    obtain ⟨h, e⟩ := δlc_spec φ ψ hφ hψ hex hsm ⟨c, hc⟩
    rw [delta₁_πlc, e]
    show continuousH2π r A _ = continuousH2π r A x
    rw [← sub_eq_zero, ← map_sub, continuousH2π_eq_zero_iff]
    simpa only [Submodule.coe_sub, neg_sub] using neg_mem hxc
  · rintro ⟨y, hy⟩
    obtain ⟨c, rfl⟩ := πlc_surjective C y
    refine ⟨(c : cocycles₁ C), c.2, ?_⟩
    obtain ⟨h, e⟩ := δlc_spec φ ψ hφ hψ hex hsm c
    rw [delta₁_πlc, e] at hy
    have : continuousH2π r A ⟨_, h⟩ - continuousH2π r A x = 0 := by rw [sub_eq_zero]; exact hy
    rw [← map_sub, continuousH2π_eq_zero_iff] at this
    simpa only [Submodule.coe_sub, neg_sub] using neg_mem this

include hφ hψ hex hsm in

lemma exact_H2_B : Function.Exact (continuousH2MapHom r φ) (continuousH2MapHom r ψ) := by
  intro z
  induction z using Submodule.Quotient.induction_on with | _ x =>
  show continuousH2MapHom r ψ (continuousH2π r B x) = 0 ↔ _
  rw [continuousH2MapHom_π, continuousH2π_eq_zero_iff, coe_levelCocycles₂Map_id,
    groupCohomology.comp_mem_levelCoboundaries2_iff_exists_levelCocycles2_sub_comp r φ ψ hφ hψ hex hsm
      (x : G × G → B) x.2]
  constructor
  · rintro ⟨a, ha, hxa⟩
    refine ⟨continuousH2π r A ⟨a, ha⟩, ?_⟩
    show continuousH2MapHom r φ (continuousH2π r A ⟨a, ha⟩) = continuousH2π r B x
    rw [continuousH2MapHom_π, ← sub_eq_zero, ← map_sub, continuousH2π_eq_zero_iff]
    simpa only [Submodule.coe_sub, coe_levelCocycles₂Map_id, neg_sub] using neg_mem hxa
  · rintro ⟨w, hw⟩
    induction w using Submodule.Quotient.induction_on with | _ a =>
    refine ⟨(a : G × G → A), a.2, ?_⟩
    have : continuousH2MapHom r φ (continuousH2π r A a) - continuousH2π r B x = 0 := by
      rw [sub_eq_zero]; exact hw
    rw [continuousH2MapHom_π, ← map_sub, continuousH2π_eq_zero_iff] at this
    simpa only [Submodule.coe_sub, coe_levelCocycles₂Map_id, neg_sub] using neg_mem this

end delta1

end P2mS26EP

open groupCohomology IntermediateField in
theorem solution
    {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsAlgClosed Ω]
    (p : ℕ) [Fact p.Prime]
    (r : (Ω ≃ₐ[K] Ω) →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (hlevel : ∀ E : IntermediateField K Ω, FiniteDimensional K E →
      ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
        ∀ σ : Ω ≃ₐ[K] Ω, r σ ∈ F.fixingSubgroup → σ ∈ E.fixingSubgroup)
    (hopen : ∀ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F →
      ∃ E : IntermediateField K Ω, FiniteDimensional K E ∧
        ∀ σ : Ω ≃ₐ[K] Ω, σ ∈ E.fixingSubgroup → r σ ∈ F.fixingSubgroup) :
    let j : continuousH2 r (Kummer.kummerRep K Ω p) →ₗ[ℤ] continuousH2 r (Rep.ofAlgebraAutOnUnits K Ω) :=
      continuousH2Map (rH := r) (rG := r) (A := Kummer.kummerRep K Ω p) (B := Rep.ofAlgebraAutOnUnits K Ω)
        (MonoidHom.id _) (fun _ => rfl)
        (MonoidHom.toAdditive (rootsOfUnity p Ω).subtype).toIntLinearMap (fun _ _ => rfl)
    Function.Injective j ∧
      ∀ x : continuousH2 r (Rep.ofAlgebraAutOnUnits K Ω), x ∈ LinearMap.range j ↔ (p : ℤ) • x = 0 := by
  classical
  intro j
  haveI : Algebra.IsAlgebraic K Ω := inferInstance

  let A : Rep ℤ (Ω ≃ₐ[K] Ω) := Kummer.kummerRep K Ω p
  let B : Rep ℤ (Ω ≃ₐ[K] Ω) := Rep.ofAlgebraAutOnUnits K Ω
  let φL : A →ₗ[ℤ] B := (MonoidHom.toAdditive (rootsOfUnity p Ω).subtype).toIntLinearMap
  have hφcomm : ∀ (σ : Ω ≃ₐ[K] Ω) (a : A), φL (A.ρ σ a) = B.ρ σ (φL a) := fun _ _ => rfl
  let φ : A ⟶ B := Rep.ofHom (φL.intertwiningMap_of_isIntertwiningMap A.ρ B.ρ hφcomm)
  let ψL : B →ₗ[ℤ] B := (MonoidHom.toAdditive (powMonoidHom p : Ωˣ →* Ωˣ)).toIntLinearMap
  have hψL : ∀ b : Additive Ωˣ, ψL b = Additive.ofMul (Additive.toMul b ^ p) := fun _ => rfl
  have hBρ : ∀ (σ : Ω ≃ₐ[K] Ω) (b : Additive Ωˣ), B.ρ σ b = Additive.ofMul (σ • Additive.toMul b) := fun _ _ => rfl
  have hψcomm : ∀ (σ : Ω ≃ₐ[K] Ω) (b : B), ψL (B.ρ σ b) = B.ρ σ (ψL b) := by
    intro σ b
    rw [hψL, hBρ, hBρ, hψL]
    simp only [toMul_ofMul, smul_pow']
  let ψ : B ⟶ B := Rep.ofHom (ψL.intertwiningMap_of_isIntertwiningMap B.ρ B.ρ hψcomm)
  have hφ_apply : ∀ a : A, φ.hom a = φL a := fun _ => rfl
  have hψ_apply : ∀ b : Additive Ωˣ, ψ.hom b = Additive.ofMul (Additive.toMul b ^ p) := fun _ => rfl
  have hφ : Function.Injective φ.hom := by
    intro a b h
    have : ((Additive.toMul a : rootsOfUnity p Ω) : Ωˣ) = ((Additive.toMul b : rootsOfUnity p Ω) : Ωˣ) :=
      congrArg Additive.toMul h
    exact Additive.toMul.injective (Subtype.ext this)
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have hψ : Function.Surjective ψ.hom := by
    intro x
    change Additive Ωˣ at x
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq ((Additive.toMul x : Ωˣ) : Ω) hp0
    have hz0 : z ≠ 0 := by
      rintro rfl; rw [zero_pow hp0.ne'] at hz; exact (Additive.toMul x).ne_zero hz.symm
    refine ⟨Additive.ofMul (Units.mk0 z hz0), ?_⟩
    rw [hψ_apply]
    apply Additive.toMul.injective
    show (Units.mk0 z hz0) ^ p = Additive.toMul x
    apply Units.ext
    simp only [Units.val_pow_eq_pow_val, Units.val_mk0, hz]
  have hex : ∀ b : B, ψ.hom b = 0 ↔ ∃ a : A, φ.hom a = b := by
    intro b
    change Additive Ωˣ at b
    rw [hψ_apply]
    constructor
    · intro h
      have h1 : Additive.toMul b ^ p = 1 := by
        have := congrArg Additive.toMul h
        rwa [toMul_ofMul] at this
      exact ⟨Additive.ofMul ⟨Additive.toMul b, (mem_rootsOfUnity _ _).2 h1⟩, rfl⟩
    · rintro ⟨a, rfl⟩
      change Additive (rootsOfUnity p Ω) at a
      have ha : ((Additive.toMul a : rootsOfUnity p Ω) : Ωˣ) ^ p = 1 := (mem_rootsOfUnity _ _).1 (Additive.toMul a).2
      show Additive.ofMul (((Additive.toMul a : rootsOfUnity p Ω) : Ωˣ) ^ p) = 0
      rw [ha]
      rfl

  have hsm : ∀ m : B, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s, r s ∈ F.fixingSubgroup → B.ρ s m = m := by
    intro m
    obtain ⟨F, hF, h⟩ := IntermediateField.exists_forall_mem_fixingSubgroup_smul_eq_of_cofinal r hlevel (Additive.toMul m)
    exact ⟨F, hF, fun s hs => by rw [hBρ, h s hs]; rfl⟩

  have hH1 : ∀ y : continuousH1 r B, y = 0 := by
    intro y
    obtain ⟨c, ⟨F, hF, hc⟩, hy⟩ := (mem_continuousH1_iff r B _).1 y.2
    obtain ⟨E, hE, hEF⟩ := hopen F hF
    haveI := hE
    let cf : (Ω ≃ₐ[K] Ω) → Additive Ωˣ := (c : (Ω ≃ₐ[K] Ω) → B)
    have hcf : ∀ g, cf g = (c : (Ω ≃ₐ[K] Ω) → B) g := fun _ => rfl
    let f : (Ω ≃ₐ[K] Ω) → Ωˣ := fun g => Additive.toMul (cf g)
    have hcoc : IsMulCocycle₁ f := by
      intro g h
      have := (mem_cocycles₁_iff (c : (Ω ≃ₐ[K] Ω) → B)).1 c.2 g h
      show Additive.toMul (cf (g * h)) = g • Additive.toMul (cf h) * Additive.toMul (cf g)
      rw [hcf, this, ← hcf, ← hcf, hBρ]
      rfl
    have hlc : ∃ E : IntermediateField K Ω, FiniteDimensional K E ∧
        ∀ σ τ : Ω ≃ₐ[K] Ω, τ ∈ E.fixingSubgroup → f (σ * τ) = f σ :=
      ⟨E, hE, fun σ τ hτ => congrArg Additive.toMul (hc σ τ (hEF τ hτ))⟩
    obtain ⟨x, hx⟩ := groupCohomology.isMulCoboundary1_of_isMulCocycle1_of_level hcoc hlc
    have hcb : ((c : (Ω ≃ₐ[K] Ω) → B)) ∈ coboundaries₁ B := by
      refine ⟨Additive.ofMul x, funext fun g => ?_⟩
      rw [d₀₁_hom_apply, ← hcf]
      have hxg : g • x / x = Additive.toMul (cf g) := hx g
      show Additive.ofMul (g • x) - Additive.ofMul x = cf g
      rw [← ofMul_div, hxg]
      rfl
    apply Subtype.ext
    rw [← hy, Submodule.coe_zero]
    exact (H1π_eq_zero_iff c).2 hcb

  have hj : ∀ z, j z = continuousH2MapHom r φ z := fun _ => rfl
  have hψp : ∀ z : continuousH2 r B, continuousH2MapHom r ψ z = (p : ℤ) • z := by
    intro z
    induction z using Submodule.Quotient.induction_on with | _ x =>
    change continuousH2π r B _ = (p : ℤ) • continuousH2π r B x
    rw [← map_smul]
    congr 1
    all_goals
      apply Subtype.ext
      funext g
      show ψ.hom ((x : (Ω ≃ₐ[K] Ω) × (Ω ≃ₐ[K] Ω) → B) g) = (p : ℤ) • (x : _ → B) g
      rw [hψ_apply, natCast_zsmul]
      exact ofMul_pow _ _
  refine ⟨?_, ?_⟩
  ·
    intro z z' hzz'
    rw [← sub_eq_zero] at hzz' ⊢
    rw [← map_sub, hj] at hzz'
    obtain ⟨y, hy⟩ := ((P2mS26EP.exact_H2_A φ ψ hφ hψ hex hsm) (z - z')).1 hzz'
    rw [← hy, hH1 y, map_zero]
  ·
    intro x
    rw [LinearMap.mem_range]
    constructor
    · rintro ⟨z, rfl⟩
      rw [← hψp, hj]
      exact ((P2mS26EP.exact_H2_B φ ψ hφ hψ hex hsm) _).2 ⟨z, rfl⟩
    · intro hx
      rw [← hψp] at hx
      obtain ⟨z, hz⟩ := ((P2mS26EP.exact_H2_B φ ψ hφ hψ hex hsm) x).1 hx
      exact ⟨z, (hj z).trans hz⟩

end S_groupCohomology_continuousH2Map_kummerRep_injective_and_range_iff_smul_eq_zero
end P2MW
export P2MW.S_groupCohomology_continuousH2Map_kummerRep_injective_and_range_iff_smul_eq_zero (solution)
