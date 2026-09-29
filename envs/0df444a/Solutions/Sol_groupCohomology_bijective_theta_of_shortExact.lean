-- Prove2me | solution 1 for groupCohomology.bijective_theta_of_shortExact
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/a7a93637-8e71-5c6d-a2d5-e4d6224e46a0

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_ContinuousH2Map
import Definitions.Def_GroupCohomology_ContinuousH1
import Definitions.Def_GroupCohomology_CupProduct
import Definitions.Def_GroupCohomology_ContinuousDuality
import Theorems.Thm_groupCohomology_deltaCochain0_mem_cocycles1_and_isLevelConstant1
import Theorems.Thm_groupCohomology_deltaCochain0_mem_coboundaries1_iff
import Theorems.Thm_groupCohomology_comp_mem_coboundaries1_iff_exists_invariants_sub_deltaCochain0
import Theorems.Thm_groupCohomology_comp_mem_coboundaries1_iff_exists_isLevelConstant1_sub_comp
import Theorems.Thm_groupCohomology_deltaCochain1_mem_levelCoboundaries2_iff
import Theorems.Thm_groupCohomology_comp_mem_levelCoboundaries2_iff_exists_sub_deltaCochain1
import Theorems.Thm_groupCohomology_comp_mem_levelCoboundaries2_iff_exists_levelCocycles2_sub_comp
import Theorems.Thm_groupCohomology_preimageFun_comp_d12_sub_deltaCochain1_mem_levelCoboundaries2
import Theorems.Thm_groupCohomology_exists_linearMap_levelCocycles1_continuousH2_eq_continuousH2pi_deltaCochain1
import Theorems.Thm_groupCohomology_cup_mem_levelCocycles2
import Theorems.Thm_groupCohomology_cup_deltaCochain0_add_cup02_deltaCochain1_mem_levelCoboundaries2
import Theorems.Thm_groupCohomology_cup20_deltaCochain1_sub_cup_deltaCochain0_mem_levelCoboundaries2
import Theorems.Thm_LinearMap_exact_dualMap_of_exact
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_bijective_theta_of_shortExact

set_option autoImplicit false
set_option maxHeartbeats 1600000

universe u

open CategoryTheory

namespace P2mS26LD7
open groupCohomology

variable {k G : Type u} [Field k] [Group G]
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

end P2mS26LD7

namespace P2mS26LD7
open groupCohomology

variable {k G : Type u} [Field k] [Group G]
  {r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)}

theorem smooth_of_injective {A B : Rep.{u} k G} (φ : A ⟶ B) (hφ : Function.Injective φ.hom)
    (hsm : ∀ m : B, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s, r s ∈ F.fixingSubgroup → B.ρ s m = m) :
    ∀ a : A, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s, r s ∈ F.fixingSubgroup → A.ρ s a = a := by
  intro a
  obtain ⟨F, hF, h⟩ := hsm (φ.hom a)
  exact ⟨F, hF, fun s hs => hφ (by rw [Rep.hom_comm_apply, h s hs])⟩

theorem smooth_of_surjective {B C : Rep.{u} k G} (ψ : B ⟶ C) (hψ : Function.Surjective ψ.hom)
    (hsm : ∀ m : B, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s, r s ∈ F.fixingSubgroup → B.ρ s m = m) :
    ∀ c : C, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s, r s ∈ F.fixingSubgroup → C.ρ s c = c := by
  intro c
  obtain ⟨b, rfl⟩ := hψ c
  obtain ⟨F, hF, h⟩ := hsm b
  exact ⟨F, hF, fun s hs => by rw [← Rep.hom_comm_apply, h s hs]⟩

variable (r)

def lc₂ {A B : Rep.{u} k G} (ψ : A ⟶ B) : levelCocycles₂ r A →ₗ[k] levelCocycles₂ r B :=
  levelCocycles₂Map (MonoidHom.id G) (fun _ => rfl) ψ.hom.toLinearMap (fun g a => Rep.hom_comm_apply ψ g a)

lemma H2map_π {A B : Rep.{u} k G} (ψ : A ⟶ B) (z : levelCocycles₂ r A) :
    continuousH2MapHom r ψ (continuousH2π r A z) = continuousH2π r B (lc₂ r ψ z) := rfl

lemma coe_lc₂ {A B : Rep.{u} k G} (ψ : A ⟶ B) (z : levelCocycles₂ r A) (st : G × G) :
    (lc₂ r ψ z : G × G → B) st = ψ.hom ((z : G × G → A) st) := rfl

def pairR {A B N : Rep.{u} k G} (ψ : A →ₗ[k] B →ₗ[k] N) (hψ : Rep.IsEquivariantBilinear A B N ψ)
    (d : B.ρ.invariants) : levelCocycles₂ r A →ₗ[k] levelCocycles₂ r N :=
  levelCocycles₂Map (MonoidHom.id G) (fun _ => rfl) (ψ.flip (d : B)) (fun g a => by
    show ψ (A.ρ g a) (d : B) = N.ρ g (ψ a (d : B))
    conv_lhs => rw [← d.2 g]
    exact hψ g a d)

lemma coe_pairR {A B N : Rep.{u} k G} (ψ : A →ₗ[k] B →ₗ[k] N) (hψ : Rep.IsEquivariantBilinear A B N ψ)
    (d : B.ρ.invariants) (z : levelCocycles₂ r A) (st : G × G) :
    (pairR r ψ hψ d z : G × G → N) st = ψ ((z : G × G → A) st) (d : B) := rfl

def pairL {A B N : Rep.{u} k G} (ψ : A →ₗ[k] B →ₗ[k] N) (hψ : Rep.IsEquivariantBilinear A B N ψ)
    (m : A.ρ.invariants) : levelCocycles₂ r B →ₗ[k] levelCocycles₂ r N :=
  levelCocycles₂Map (MonoidHom.id G) (fun _ => rfl) (ψ (m : A)) (fun g b => by
    show ψ (m : A) (B.ρ g b) = N.ρ g (ψ (m : A) b)
    conv_lhs => rw [← m.2 g]
    exact hψ g m b)

lemma coe_pairL {A B N : Rep.{u} k G} (ψ : A →ₗ[k] B →ₗ[k] N) (hψ : Rep.IsEquivariantBilinear A B N ψ)
    (m : A.ρ.invariants) (z : levelCocycles₂ r B) (st : G × G) :
    (pairL r ψ hψ m z : G × G → N) st = ψ (m : A) ((z : G × G → B) st) := rfl

lemma mapH1_mk {A B : Rep.{u} k G} (ψ : A ⟶ B) (c : cocycles₁ A) (hc : IsLevelConstant₁ r c) :
    mapH1 r ψ ⟨(H1π A).hom c, H1π_mem_continuousH1 r A hc⟩
      = ⟨(H1π B).hom (mapCocycles₁ (MonoidHom.id G) ψ c), H1π_mem_continuousH1 r B (hc.comp ψ.hom)⟩ :=
  Subtype.ext (map_hom_H1π_hom ψ c)

lemma exists_rep' {A : Rep.{u} k G} (x : continuousH1 r A) :
    ∃ c : cocycles₁ A, ∃ hc : IsLevelConstant₁ r c, x = ⟨(H1π A).hom c, H1π_mem_continuousH1 r A hc⟩ := by
  obtain ⟨c, hc, hx⟩ := (mem_continuousH1_iff r A _).1 x.2
  exact ⟨c, hc, Subtype.ext hx.symm⟩

lemma inv_eq_neg_of_add_mem {N : Rep.{u} k G} (inv : continuousH2 r N →ₗ[k] k) (e₁ e₂ : levelCocycles₂ r N)
    (h : ((e₁ : G × G → N) + (e₂ : G × G → N)) ∈ levelCoboundaries₂ r N) :
    inv (continuousH2π r N e₁) = - inv (continuousH2π r N e₂) := by
  have : continuousH2π r N e₁ = - continuousH2π r N e₂ := by
    rw [eq_neg_iff_add_eq_zero, ← map_add, continuousH2π_eq_zero_iff]
    exact h
  rw [this, map_neg]

lemma inv_eq_of_sub_mem {N : Rep.{u} k G} (inv : continuousH2 r N →ₗ[k] k) (e₁ e₂ : levelCocycles₂ r N)
    (h : ((e₁ : G × G → N) - (e₂ : G × G → N)) ∈ levelCoboundaries₂ r N) :
    inv (continuousH2π r N e₁) = inv (continuousH2π r N e₂) := by
  congr 1
  rw [← sub_eq_zero, ← map_sub, continuousH2π_eq_zero_iff]
  exact h

end P2mS26LD7

open P2mS26LD7 groupCohomology in
theorem solution
    {k G : Type u} [Field k] [Group G]
    (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    {M' M M'' D'' D D' N : Rep.{u} k G}
    (i : M' ⟶ M) (π : M ⟶ M'') (hi : Function.Injective i.hom) (hπ : Function.Surjective π.hom)
    (hex : ∀ m : M, π.hom m = 0 ↔ ∃ m' : M', i.hom m' = m)
    (πD : D'' ⟶ D) (iD : D ⟶ D') (hπD : Function.Injective πD.hom) (hiD : Function.Surjective iD.hom)
    (hexD : ∀ x : D, iD.hom x = 0 ↔ ∃ y : D'', πD.hom y = x)
    (hsmM : ∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s, r s ∈ F.fixingSubgroup → M.ρ s m = m)
    (hsmD : ∀ x : D, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s, r s ∈ F.fixingSubgroup → D.ρ s x = x)
    (φ' : M' →ₗ[k] D' →ₗ[k] N)
    (φ : M →ₗ[k] D →ₗ[k] N) (hφ : Rep.IsEquivariantBilinear M D N φ)
    (φ'' : M'' →ₗ[k] D'' →ₗ[k] N)
    (hcompat_i : ∀ (m' : M') (x : D), φ (i.hom m') x = φ' m' (iD.hom x))
    (hcompat_π : ∀ (m : M) (y : D''), φ m (πD.hom y) = φ'' (π.hom m) y)
    (inv : continuousH2 r N →ₗ[k] k)
    (hD2π : Function.Surjective (continuousH2MapHom r π))
    (hD2iD : Function.Surjective (continuousH2MapHom r iD))
    (θ₀' : M'.ρ.invariants →ₗ[k] Module.Dual k (continuousH2 r D')) (hθ₀' : IsTheta0 r φ' inv θ₀')
    (θ₁' : continuousH1 r M' →ₗ[k] Module.Dual k (continuousH1 r D')) (hθ₁' : IsTheta1 r φ' inv θ₁')
    (θ₂' : continuousH2 r M' →ₗ[k] Module.Dual k D'.ρ.invariants) (hθ₂' : IsTheta2 r φ' inv θ₂')
    (θ₀ : M.ρ.invariants →ₗ[k] Module.Dual k (continuousH2 r D)) (hθ₀ : IsTheta0 r φ inv θ₀)
    (θ₁ : continuousH1 r M →ₗ[k] Module.Dual k (continuousH1 r D)) (hθ₁ : IsTheta1 r φ inv θ₁)
    (θ₂ : continuousH2 r M →ₗ[k] Module.Dual k D.ρ.invariants) (hθ₂ : IsTheta2 r φ inv θ₂)
    (θ₀'' : M''.ρ.invariants →ₗ[k] Module.Dual k (continuousH2 r D'')) (hθ₀'' : IsTheta0 r φ'' inv θ₀'')
    (θ₁'' : continuousH1 r M'' →ₗ[k] Module.Dual k (continuousH1 r D'')) (hθ₁'' : IsTheta1 r φ'' inv θ₁'')
    (θ₂'' : continuousH2 r M'' →ₗ[k] Module.Dual k D''.ρ.invariants) (hθ₂'' : IsTheta2 r φ'' inv θ₂'')
    (h' : Function.Bijective θ₀' ∧ Function.Bijective θ₁' ∧ Function.Bijective θ₂')
    (h'' : Function.Bijective θ₀'' ∧ Function.Bijective θ₁'' ∧ Function.Bijective θ₂'') :
    Function.Bijective θ₀ ∧ Function.Bijective θ₁ ∧ Function.Bijective θ₂ := by

  have hφ' : Rep.IsEquivariantBilinear M' D' N φ' := by
    intro g m' x'
    obtain ⟨x, rfl⟩ := hiD x'
    rw [← Rep.hom_comm_apply iD g x, ← hcompat_i, ← hcompat_i, Rep.hom_comm_apply i g m', hφ]
  have hφ'' : Rep.IsEquivariantBilinear M'' D'' N φ'' := by
    intro g m'' y
    obtain ⟨m, rfl⟩ := hπ m''
    rw [← Rep.hom_comm_apply π g m, ← hcompat_π, ← hcompat_π, Rep.hom_comm_apply πD g y, hφ]
  classical
  obtain ⟨hb0', hb1', hb2'⟩ := h'
  obtain ⟨hb0'', hb1'', hb2''⟩ := h''

  have hsmM' := smooth_of_injective (r := r) i hi hsmM
  have hsmM'' := smooth_of_surjective (r := r) π hπ hsmM
  have hsmD'' := smooth_of_injective (r := r) πD hπD hsmD
  have hsmD' := smooth_of_surjective (r := r) iD hiD hsmD

  let f₁ := inv₀ i
  let f₂ := inv₀ π
  let f₃ := delta₀ r i π hi hπ hex hsmM
  let f₄ := mapH1 r i
  let f₅ := mapH1 r π
  let f₆ := delta₁ r i π hi hπ hex hsmM
  let f₇ := continuousH2MapHom r i
  let f₈ := continuousH2MapHom r π
  have e₂ : Function.Exact f₁ f₂ := exact_inv₀ i π hi hex
  have e₃ : Function.Exact f₂ f₃ := exact_delta₀ i π hi hπ hex hsmM
  have e₄ : Function.Exact f₃ f₄ := exact_mapH1_A i π hi hπ hex hsmM
  have e₅ : Function.Exact f₄ f₅ := exact_mapH1_B i π hi hπ hex hsmM
  have e₆ : Function.Exact f₅ f₆ := exact_delta₁ i π hi hπ hex hsmM
  have e₇ : Function.Exact f₆ f₇ := exact_H2_A i π hi hπ hex hsmM
  have e₈ : Function.Exact f₇ f₈ := exact_H2_B i π hi hπ hex hsmM

  let F₁ := inv₀ πD
  let F₂ := inv₀ iD
  let F₃ := delta₀ r πD iD hπD hiD hexD hsmD
  let F₄ := mapH1 r πD
  let F₅ := mapH1 r iD
  let F₆ := delta₁ r πD iD hπD hiD hexD hsmD
  let F₇ := continuousH2MapHom r πD
  let F₈ := continuousH2MapHom r iD
  have E₂ : Function.Exact F₁ F₂ := exact_inv₀ πD iD hπD hexD
  have E₃ : Function.Exact F₂ F₃ := exact_delta₀ πD iD hπD hiD hexD hsmD
  have E₄ : Function.Exact F₃ F₄ := exact_mapH1_A πD iD hπD hiD hexD hsmD
  have E₅ : Function.Exact F₄ F₅ := exact_mapH1_B πD iD hπD hiD hexD hsmD
  have E₆ : Function.Exact F₅ F₆ := exact_delta₁ πD iD hπD hiD hexD hsmD
  have E₇ : Function.Exact F₆ F₇ := exact_H2_A πD iD hπD hiD hexD hsmD
  have E₈ : Function.Exact F₇ F₈ := exact_H2_B πD iD hπD hiD hexD hsmD
  let g₁ := F₈.dualMap
  let g₂ := F₇.dualMap
  let g₃ := F₆.dualMap
  let g₄ := F₅.dualMap
  let g₅ := F₄.dualMap
  let g₆ := F₃.dualMap
  let g₇ := F₂.dualMap
  let g₈ := F₁.dualMap
  have d₂ : Function.Exact g₁ g₂ := LinearMap.exact_dualMap_of_exact _ _ E₈
  have d₃ : Function.Exact g₂ g₃ := LinearMap.exact_dualMap_of_exact _ _ E₇
  have d₄ : Function.Exact g₃ g₄ := LinearMap.exact_dualMap_of_exact _ _ E₆
  have d₅ : Function.Exact g₄ g₅ := LinearMap.exact_dualMap_of_exact _ _ E₅
  have d₆ : Function.Exact g₅ g₆ := LinearMap.exact_dualMap_of_exact _ _ E₄
  have d₇ : Function.Exact g₆ g₇ := LinearMap.exact_dualMap_of_exact _ _ E₃
  have d₈ : Function.Exact g₇ g₈ := LinearMap.exact_dualMap_of_exact _ _ E₂

  have S1 : g₁ ∘ₗ (-θ₀') = (-θ₀) ∘ₗ f₁ := by
    apply LinearMap.ext; intro m'; apply LinearMap.ext; intro w
    induction w using Submodule.Quotient.induction_on with | _ z =>
    show -(θ₀' m' (continuousH2MapHom r iD (continuousH2π r D z))) = -(θ₀ (inv₀ i m') (continuousH2π r D z))
    rw [H2map_π, hθ₀ (inv₀ i m') z (pairL r φ hφ (inv₀ i m') z) (fun st => rfl),
      hθ₀' m' (lc₂ r iD z) (pairL r φ hφ (inv₀ i m') z) (fun st => ?_)]
    rw [coe_pairL, coe_lc₂, coe_inv₀, hcompat_i]
  have S2 : g₂ ∘ₗ (-θ₀) = (-θ₀'') ∘ₗ f₂ := by
    apply LinearMap.ext; intro m; apply LinearMap.ext; intro w
    induction w using Submodule.Quotient.induction_on with | _ z =>
    show -(θ₀ m (continuousH2MapHom r πD (continuousH2π r D'' z))) = -(θ₀'' (inv₀ π m) (continuousH2π r D'' z))
    rw [H2map_π, hθ₀'' (inv₀ π m) z (pairL r φ'' hφ'' (inv₀ π m) z) (fun st => rfl),
      hθ₀ m (lc₂ r πD z) (pairL r φ'' hφ'' (inv₀ π m) z) (fun st => ?_)]
    rw [coe_pairL, coe_lc₂, coe_inv₀, hcompat_π]
  have S3 : g₃ ∘ₗ (-θ₀'') = θ₁' ∘ₗ f₃ := by
    apply LinearMap.ext; intro c; apply LinearMap.ext; intro y
    obtain ⟨yc, hyc, rfl⟩ := exists_rep' r y
    show -(θ₀'' c (delta₁ r πD iD hπD hiD hexD hsmD (πlc r D' ⟨yc, hyc⟩)))
      = θ₁' (delta₀ r i π hi hπ hex hsmM c) ⟨(H1π D').hom yc, H1π_mem_continuousH1 r D' hyc⟩
    rw [delta₁_πlc πD iD hπD hiD hexD hsmD]
    obtain ⟨hz, hz'⟩ := δlc_spec πD iD hπD hiD hexD hsmD ⟨yc, hyc⟩
    rw [hz']

    have hδ := groupCohomology.deltaCochain0_mem_cocycles1_and_isLevelConstant1 r i π hi hπ hex hsmM c c.2
    let e₁ : levelCocycles₂ r N := ⟨cupCochain φ' (deltaCochain₀ i π hπ c) (⇑yc), by
      have := groupCohomology.cup_mem_levelCocycles2 r φ' hφ' hsmD' ⟨deltaCochain₀ i π hπ c, hδ.1⟩ yc hδ.2 hyc
      rwa [cup_coe] at this⟩
    let e₂ : levelCocycles₂ r N := pairL r φ'' hφ'' c ⟨deltaCochain₁ πD iD hiD (⇑yc), hz⟩
    rw [hθ₀'' c ⟨deltaCochain₁ πD iD hiD (⇑yc), hz⟩ e₂ (fun st => rfl)]
    have h1 : θ₁' (delta₀ r i π hi hπ hex hsmM c) ⟨(H1π D').hom yc, H1π_mem_continuousH1 r D' hyc⟩
        = inv (continuousH2π r N e₁) :=
      hθ₁' ⟨deltaCochain₀ i π hπ c, hδ.1⟩ hδ.2 yc hyc e₁ (fun _ => rfl)
    rw [h1, inv_eq_neg_of_add_mem r inv e₁ e₂]
    exact groupCohomology.cup_deltaCochain0_add_cup02_deltaCochain1_mem_levelCoboundaries2 r i π hπ hex πD iD hiD hexD
      φ' φ hφ φ'' hcompat_i hcompat_π c c.2 yc hyc
  have S4 : g₄ ∘ₗ θ₁' = θ₁ ∘ₗ f₄ := by
    apply LinearMap.ext; intro x'; apply LinearMap.ext; intro y
    obtain ⟨f', hf', rfl⟩ := exists_rep' r x'
    obtain ⟨g, hg, rfl⟩ := exists_rep' r y
    show θ₁' _ (mapH1 r iD _) = θ₁ (mapH1 r i _) _
    rw [mapH1_mk r iD g hg, mapH1_mk r i f' hf']
    let e : levelCocycles₂ r N := ⟨cupCochain φ (⇑(mapCocycles₁ (MonoidHom.id G) i f')) (⇑g), by
      have := groupCohomology.cup_mem_levelCocycles2 r φ hφ hsmD (mapCocycles₁ (MonoidHom.id G) i f') g (hf'.comp i.hom) hg
      rwa [cup_coe] at this⟩
    rw [hθ₁ _ (hf'.comp i.hom) g hg e (fun _ => rfl), hθ₁' f' hf' _ (hg.comp iD.hom) e ?_]
    rintro ⟨s, t⟩
    show φ (i.hom (f' s)) (D.ρ s (g t)) = φ' (f' s) (D'.ρ s (iD.hom (g t)))
    rw [← Rep.hom_comm_apply, hcompat_i]
  have S5 : g₅ ∘ₗ θ₁ = θ₁'' ∘ₗ f₅ := by
    apply LinearMap.ext; intro x; apply LinearMap.ext; intro y''
    obtain ⟨f, hf, rfl⟩ := exists_rep' r x
    obtain ⟨g'', hg'', rfl⟩ := exists_rep' r y''
    show θ₁ _ (mapH1 r πD _) = θ₁'' (mapH1 r π _) _
    rw [mapH1_mk r πD g'' hg'', mapH1_mk r π f hf]
    let e : levelCocycles₂ r N := ⟨cupCochain φ'' (⇑(mapCocycles₁ (MonoidHom.id G) π f)) (⇑g''), by
      have := groupCohomology.cup_mem_levelCocycles2 r φ'' hφ'' hsmD'' (mapCocycles₁ (MonoidHom.id G) π f) g''
        (hf.comp π.hom) hg''
      rwa [cup_coe] at this⟩
    rw [hθ₁'' _ (hf.comp π.hom) g'' hg'' e (fun _ => rfl), hθ₁ f hf _ (hg''.comp πD.hom) e ?_]
    rintro ⟨s, t⟩
    show φ'' (π.hom (f s)) (D''.ρ s (g'' t)) = φ (f s) (D.ρ s (πD.hom (g'' t)))
    rw [← Rep.hom_comm_apply, hcompat_π]
  have S6 : g₆ ∘ₗ θ₁'' = θ₂' ∘ₗ f₆ := by
    apply LinearMap.ext; intro x''; apply LinearMap.ext; intro d'
    obtain ⟨c, hc, rfl⟩ := exists_rep' r x''
    show θ₁'' _ (delta₀ r πD iD hπD hiD hexD hsmD d') = θ₂' (delta₁ r i π hi hπ hex hsmM _) d'
    have hx : (⟨(H1π M'').hom c, H1π_mem_continuousH1 r M'' hc⟩ : continuousH1 r M'') = πlc r M'' ⟨c, hc⟩ := rfl
    rw [hx, delta₁_πlc i π hi hπ hex hsmM]
    obtain ⟨hz, hz'⟩ := δlc_spec i π hi hπ hex hsmM ⟨c, hc⟩
    rw [hz']
    have hδ := groupCohomology.deltaCochain0_mem_cocycles1_and_isLevelConstant1 r πD iD hπD hiD hexD hsmD d' d'.2
    let e₃ : levelCocycles₂ r N := pairR r φ' hφ' d' ⟨deltaCochain₁ i π hπ (⇑c), hz⟩
    let e₄ : levelCocycles₂ r N := ⟨cupCochain φ'' (⇑c) (deltaCochain₀ πD iD hiD d'), by
      have := groupCohomology.cup_mem_levelCocycles2 r φ'' hφ'' hsmD'' c ⟨deltaCochain₀ πD iD hiD d', hδ.1⟩ hc hδ.2
      rwa [cup_coe] at this⟩
    rw [hθ₂' ⟨deltaCochain₁ i π hπ (⇑c), hz⟩ d' e₃ (fun st => rfl)]
    have h1 : θ₁'' (πlc r M'' ⟨c, hc⟩) (delta₀ r πD iD hπD hiD hexD hsmD d') = inv (continuousH2π r N e₄) :=
      hθ₁'' c hc ⟨deltaCochain₀ πD iD hiD d', hδ.1⟩ hδ.2 e₄ (fun _ => rfl)
    rw [h1]
    refine (inv_eq_of_sub_mem r inv e₃ e₄ ?_).symm
    have h4d := groupCohomology.cup20_deltaCochain1_sub_cup_deltaCochain0_mem_levelCoboundaries2 r i π hπ hex πD iD hiD hexD
      φ' φ hφ φ'' hcompat_i hcompat_π hsmD c hc d' d'.2
    have heq : (fun st : G × G => φ' (deltaCochain₁ i π hπ (⇑c) st) (D'.ρ (st.1 * st.2) d')) = (e₃ : G × G → N) := by
      funext st
      rw [coe_pairR, d'.2 (st.1 * st.2)]
    rwa [heq] at h4d
  have S7 : g₇ ∘ₗ θ₂' = θ₂ ∘ₗ f₇ := by
    apply LinearMap.ext; intro w'; apply LinearMap.ext; intro d
    induction w' using Submodule.Quotient.induction_on with | _ z' =>
    show θ₂' (continuousH2π r M' z') (inv₀ iD d) = θ₂ (continuousH2MapHom r i (continuousH2π r M' z')) d
    rw [H2map_π, hθ₂' z' (inv₀ iD d) (pairR r φ' hφ' (inv₀ iD d) z') (fun st => rfl),
      hθ₂ (lc₂ r i z') d (pairR r φ' hφ' (inv₀ iD d) z') (fun st => ?_)]
    rw [coe_pairR, coe_lc₂, coe_inv₀, hcompat_i]
  have S8 : g₈ ∘ₗ θ₂ = θ₂'' ∘ₗ f₈ := by
    apply LinearMap.ext; intro w; apply LinearMap.ext; intro d''
    induction w using Submodule.Quotient.induction_on with | _ z =>
    show θ₂ (continuousH2π r M z) (inv₀ πD d'') = θ₂'' (continuousH2MapHom r π (continuousH2π r M z)) d''
    rw [H2map_π, hθ₂ z (inv₀ πD d'') (pairR r φ hφ (inv₀ πD d'') z) (fun st => rfl),
      hθ₂'' (lc₂ r π z) d'' (pairR r φ hφ (inv₀ πD d'') z) (fun st => ?_)]
    rw [coe_pairR, coe_lc₂, coe_inv₀, hcompat_π]

  have hneg : ∀ {X Y : Type u} [AddCommGroup X] [Module k X] [AddCommGroup Y] [Module k Y] (T : X →ₗ[k] Y),
      Function.Bijective T → Function.Bijective (-T) := fun T hT =>
    ⟨fun x y hxy => hT.1 (neg_injective hxy), fun y => by obtain ⟨x, hx⟩ := hT.2 (-y); exact ⟨x, by simp [hx]⟩⟩
  refine ⟨⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩⟩
  ·
    intro m₁ m₂ hm
    rw [← sub_eq_zero] at hm ⊢
    set m := m₁ - m₂ with hmdef
    have hm0 : θ₀ m = 0 := by rw [hmdef, map_sub, hm]
    have h2 : θ₀'' (f₂ m) = 0 := by
      have := congrArg (fun T => T m) S2
      simp only [LinearMap.comp_apply, LinearMap.neg_apply, hm0, neg_zero, map_zero] at this
      exact neg_eq_zero.1 this.symm
    have hm2 : f₂ m = 0 := hb0''.1 (by rw [h2, map_zero])
    obtain ⟨m', hm'⟩ := (e₂ m).1 hm2
    have h1 : g₁ (θ₀' m') = 0 := by
      have := congrArg (fun T => T m') S1
      simp only [LinearMap.comp_apply, LinearMap.neg_apply, map_neg, neg_inj] at this
      rw [this, hm', hm0]
    have h1' : θ₀' m' = 0 := LinearMap.dualMap_injective_of_surjective hD2iD h1
    have : m' = 0 := hb0'.1 (by rw [h1', map_zero])
    rw [← hm', this, map_zero]
  ·
    have := LinearMap.surjective_of_surjective_of_surjective_of_injective f₁ f₂ f₃ g₁ g₂ g₃ (-θ₀') (-θ₀) (-θ₀'') θ₁'
      S1 S2 S3 e₃ d₂ d₃ (hneg _ hb0').2 (hneg _ hb0'').2 hb1'.1
    exact fun y => by obtain ⟨x, hx⟩ := this (-y); exact ⟨x, by simpa using hx⟩
  ·
    exact LinearMap.bijective_of_surjective_of_bijective_of_bijective_of_injective f₃ f₄ f₅ f₆ g₃ g₄ g₅ g₆
      (-θ₀'') θ₁' θ₁ θ₁'' θ₂' S3 S4 S5 S6 e₄ e₅ e₆ d₄ d₅ d₆ (hneg _ hb0'').2 hb1' hb1'' hb2'.1
  ·
    exact LinearMap.injective_of_surjective_of_injective_of_injective f₆ f₇ f₈ g₆ g₇ g₈ θ₁'' θ₂' θ₂ θ₂''
      S6 S7 S8 e₇ e₈ d₇ hb1''.2 hb2'.1 hb2''.1
  ·
    intro ψ
    obtain ⟨w'', hw''⟩ := hb2''.2 (g₈ ψ)
    obtain ⟨w, rfl⟩ := hD2π w''
    have h8 : g₈ (θ₂ w - ψ) = 0 := by
      have := congrArg (fun T => T w) S8
      simp only [LinearMap.comp_apply] at this
      rw [map_sub, this, hw'', sub_self]
    obtain ⟨χ, hχ⟩ := (d₈ _).1 h8
    obtain ⟨w', hw'⟩ := hb2'.2 χ
    have h7 : g₇ (θ₂' w') = θ₂ (f₇ w') := by
      have := congrArg (fun T => T w') S7
      simpa only [LinearMap.comp_apply] using this
    refine ⟨w - f₇ w', ?_⟩
    rw [map_sub, ← h7, hw', hχ, sub_sub_cancel]

end S_groupCohomology_bijective_theta_of_shortExact
end P2MW
export P2MW.S_groupCohomology_bijective_theta_of_shortExact (solution)
