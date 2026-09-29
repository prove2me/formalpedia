-- Prove2me | solution 1 for groupCohomology.exists_les_continuousHS_of_shortExact_of_isLevelConstant
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/618b15f9-320e-5044-a8ec-14f855e90428

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Theorems.Thm_groupCohomology_exists_isUnramifiedOutside_forall_apply_eq_one_of_smooth
import Theorems.Thm_IntermediateField_IsUnramifiedOutside_normalClosure
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_exists_les_continuousHS_of_shortExact_of_isLevelConstant

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000
open CategoryTheory Module groupCohomology ExtCitation

local instance P2mS25LES8.isAlgebraicQbar : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) :=
  AlgebraicClosure.isAlgebraic ℚ
local instance P2mS25LES8.isAlgClosureQbar : IsAlgClosure ℚ (AlgebraicClosure ℚ) := ⟨inferInstance, inferInstance⟩
local instance P2mS25LES8.normalQbar : Normal ℚ (AlgebraicClosure ℚ) := IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)

namespace P2mS25LES8

local notation "Γ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

lemma conj_mem_fixingSubgroup (E : IntermediateField ℚ (AlgebraicClosure ℚ)) [hE : Normal ℚ E]
    {s : Γ} (hs : s ∈ E.fixingSubgroup) (h : Γ) : h⁻¹ * s * h ∈ E.fixingSubgroup := by
  rw [IntermediateField.mem_fixingSubgroup_iff] at hs ⊢
  intro x hx
  have hhx : h x ∈ E := (IntermediateField.normal_iff_forall_map_le'.1 hE h) ⟨x, hx, rfl⟩
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hs _ hhx]
  simp

lemma exists_normal_level {S : Finset Nat.Primes} {X : Type*} {b : Γ → X}
    (hb : IsLevelConstantS₁ S b) :
    ∃ E : IntermediateField ℚ (AlgebraicClosure ℚ), E.IsUnramifiedOutside S ∧ Normal ℚ E ∧
      ∀ g s, s ∈ E.fixingSubgroup → b (g * s) = b g := by
  obtain ⟨F, hF, h⟩ := hb
  refine ⟨IntermediateField.normalClosure ℚ F (AlgebraicClosure ℚ), hF.normalClosure,
    normalClosure.normal ℚ F _, fun g s hs => ?_⟩
  exact h g s (IntermediateField.fixingSubgroup_antitone (IntermediateField.le_normalClosure F) hs)

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

lemma lcS₁_orbit {L : IntermediateField ℚ (AlgebraicClosure ℚ)} (hLS : L.IsUnramifiedOutside S)
    (hL : ∀ s ∈ L.fixingSubgroup, A.ρ s = 1) (m : A) : IsLevelConstantS₁ S (fun g => A.ρ g m) :=
  ⟨L, hLS, fun g s hs => by
    show A.ρ (g * s) m = A.ρ g m
    rw [map_mul, Module.End.mul_apply, hL s hs, Module.End.one_apply]⟩

lemma lcS₁_d₀₁ {L : IntermediateField ℚ (AlgebraicClosure ℚ)} (hLS : L.IsUnramifiedOutside S)
    (hL : ∀ s ∈ L.fixingSubgroup, A.ρ s = 1) (m : A) : IsLevelConstantS₁ S ((d₀₁ A).hom m) := by
  refine ⟨L, hLS, fun g s hs => ?_⟩
  rw [d₀₁_hom_apply, d₀₁_hom_apply, map_mul, Module.End.mul_apply, hL s hs, Module.End.one_apply]

lemma lcS₂_d₁₂ {L : IntermediateField ℚ (AlgebraicClosure ℚ)} (hLS : L.IsUnramifiedOutside S)
    (hL : ∀ s ∈ L.fixingSubgroup, A.ρ s = 1) {b : Γ → A} (hb : IsLevelConstantS₁ S b) :
    IsLevelConstantS₂ S ((d₁₂ A).hom b) := by
  obtain ⟨E, hE, hEn, h⟩ := exists_normal_level hb
  haveI := hEn
  refine ⟨E ⊔ L, hE.sup hLS, fun g g' s s' hs hs' => ?_⟩
  have hsE : s ∈ E.fixingSubgroup := IntermediateField.fixingSubgroup_antitone le_sup_left hs
  have hs'E : s' ∈ E.fixingSubgroup := IntermediateField.fixingSubgroup_antitone le_sup_left hs'
  have hsL : s ∈ L.fixingSubgroup := IntermediateField.fixingSubgroup_antitone le_sup_right hs
  simp only [d₁₂_hom_apply]
  have e1 : g * s * (g' * s') = g * g' * (g'⁻¹ * s * g' * s') := by group
  rw [e1, h (g * g') _ (E.fixingSubgroup.mul_mem (conj_mem_fixingSubgroup E hsE g') hs'E), h g' s' hs'E, h g s hsE,
    map_mul, Module.End.mul_apply, hL s hsL, Module.End.one_apply]

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

structure Ctx (k : Type) [Field k] (S : Finset Nat.Primes) where
  N1 : Rep.{0} k Γ
  N2 : Rep.{0} k Γ
  N3 : Rep.{0} k Γ
  f : N1 ⟶ N2
  g : N2 ⟶ N3
  hφ : Function.Injective f.hom
  hex : ∀ b : N2, g.hom b = 0 ↔ ∃ a : N1, f.hom a = b
  σ : N3 →ₗ[k] N2
  hσ : ∀ x, g.hom (σ x) = x
  π : N2 →ₗ[k] N1
  hπ : ∀ a, π (f.hom a) = a
  L : IntermediateField ℚ (AlgebraicClosure ℚ)
  hLS : L.IsUnramifiedOutside S
  hL2 : ∀ s ∈ L.fixingSubgroup, N2.ρ s = 1

section ctx

variable {k : Type} [Field k] {S : Finset Nat.Primes} (C : Ctx k S)

lemma Ctx.gf (a : C.N1) : C.g.hom (C.f.hom a) = 0 := (C.hex _).2 ⟨a, rfl⟩

lemma Ctx.fπ {b : C.N2} (hb : C.g.hom b = 0) : C.f.hom (C.π b) = b := by
  obtain ⟨a, rfl⟩ := (C.hex b).1 hb
  rw [C.hπ]

lemma Ctx.hL1 : ∀ s ∈ C.L.fixingSubgroup, C.N1.ρ s = 1 := fun s hs => by
  refine LinearMap.ext fun a => C.hφ ?_
  rw [Rep.hom_comm_apply, C.hL2 s hs]
  rfl

lemma Ctx.hL3 : ∀ s ∈ C.L.fixingSubgroup, C.N3.ρ s = 1 := fun s hs => by
  refine LinearMap.ext fun x => ?_
  conv_lhs => rw [← C.hσ x]
  rw [← Rep.hom_comm_apply, C.hL2 s hs, Module.End.one_apply, Module.End.one_apply, C.hσ]

noncomputable def i₀ : C.N1.ρ.invariants →ₗ[k] C.N2.ρ.invariants :=
  (C.f.hom.toLinearMap ∘ₗ C.N1.ρ.invariants.subtype).codRestrict _ fun x γ => by
    show C.N2.ρ γ (C.f.hom x) = C.f.hom x
    rw [← Rep.hom_comm_apply, x.2 γ]

lemma coe_i₀ (x : C.N1.ρ.invariants) : (i₀ C x : C.N2) = C.f.hom x := rfl

noncomputable def p₀ : C.N2.ρ.invariants →ₗ[k] C.N3.ρ.invariants :=
  (C.g.hom.toLinearMap ∘ₗ C.N2.ρ.invariants.subtype).codRestrict _ fun x γ => by
    show C.N3.ρ γ (C.g.hom x) = C.g.hom x
    rw [← Rep.hom_comm_apply, x.2 γ]

lemma coe_p₀ (x : C.N2.ρ.invariants) : (p₀ C x : C.N3) = C.g.hom x := rfl

noncomputable def δ₀c : C.N3 →ₗ[k] (Γ → C.N1) := C.π.compLeft Γ ∘ₗ (d₀₁ C.N2).hom ∘ₗ C.σ

lemma δ₀c_eq (x : C.N3) : δ₀c C x = C.π ∘ (d₀₁ C.N2).hom (C.σ x) := rfl

lemma δ₀c_apply (x : C.N3) (γ : Γ) : δ₀c C x γ = C.π (C.N2.ρ γ (C.σ x) - C.σ x) := by
  rw [δ₀c_eq, Function.comp_apply, d₀₁_hom_apply]

lemma g_d₀₁σ {x : C.N3} (hx : x ∈ C.N3.ρ.invariants) (γ : Γ) : C.g.hom (C.N2.ρ γ (C.σ x) - C.σ x) = 0 := by
  rw [map_sub, Rep.hom_comm_apply, C.hσ, hx γ, sub_self]

lemma f_δ₀c {x : C.N3} (hx : x ∈ C.N3.ρ.invariants) (γ : Γ) :
    C.f.hom (δ₀c C x γ) = C.N2.ρ γ (C.σ x) - C.σ x := by
  rw [δ₀c_apply, C.fπ (g_d₀₁σ C hx γ)]

lemma f_comp_δ₀c {x : C.N3} (hx : x ∈ C.N3.ρ.invariants) :
    C.f.hom ∘ δ₀c C x = (d₀₁ C.N2).hom (C.σ x) :=
  funext fun γ => by rw [Function.comp_apply, f_δ₀c C hx, d₀₁_hom_apply]

lemma δ₀c_mem_cocycles₁ {x : C.N3} (hx : x ∈ C.N3.ρ.invariants) : δ₀c C x ∈ cocycles₁ C.N1 := by
  show (d₁₂ C.N1).hom (δ₀c C x) = 0
  apply comp_injective C.f C.hφ
  rw [← d₁₂_comp, f_comp_δ₀c C hx, d₁₂_d₀₁]
  funext st
  exact (map_zero C.f.hom).symm

lemma δ₀c_lcS₁ (x : C.N3) : IsLevelConstantS₁ S (δ₀c C x) := by
  rw [δ₀c_eq]
  exact (lcS₁_d₀₁ C.hLS C.hL2 _).comp _

noncomputable def δ₀z : C.N3.ρ.invariants →ₗ[k] cocycles₁ C.N1 :=
  (δ₀c C ∘ₗ C.N3.ρ.invariants.subtype).codRestrict _ fun x => δ₀c_mem_cocycles₁ C x.2

lemma coe_δ₀z (x : C.N3.ρ.invariants) : (δ₀z C x : Γ → C.N1) = δ₀c C x := rfl

noncomputable def delta₀ : C.N3.ρ.invariants →ₗ[k] continuousH1S S C.N1 :=
  ((H1π C.N1).hom ∘ₗ δ₀z C).codRestrict _ fun x =>
    (mem_continuousH1S_iff S _ _).2 ⟨δ₀z C x, δ₀c_lcS₁ C (x : C.N3), rfl⟩

lemma coe_delta₀ (x : C.N3.ρ.invariants) : (delta₀ C x : H1 C.N1) = (H1π C.N1).hom (δ₀z C x) := rfl

lemma delta₀_pin (x : C.N3.ρ.invariants) (y : C.N2) (c : cocycles₁ C.N1) (hy : C.g.hom y = (x : C.N3))
    (hc : ∀ s, C.f.hom (c s) = C.N2.ρ s y - y) :
    (delta₀ C x : H1 C.N1) = (H1π C.N1).hom c := by
  rw [coe_delta₀, H1π_hom_eq_iff]
  refine ⟨C.π (C.σ x - y), funext fun s => C.hφ ?_⟩
  have hker : C.g.hom (C.σ x - y) = 0 := by rw [map_sub, C.hσ, hy, sub_self]
  rw [d₀₁_hom_apply, map_sub C.f.hom, Rep.hom_comm_apply, C.fπ hker, Pi.sub_apply, map_sub C.f.hom, coe_δ₀z,
    f_δ₀c C x.2, hc, map_sub]
  abel

noncomputable def Δ₁ : cocycles₁ C.N3 →ₗ[k] (Γ × Γ → C.N1) :=
  C.π.compLeft (Γ × Γ) ∘ₗ (d₁₂ C.N2).hom ∘ₗ C.σ.compLeft Γ ∘ₗ (cocycles₁ C.N3).subtype

lemma Δ₁_eq (c : cocycles₁ C.N3) : Δ₁ C c = C.π ∘ (d₁₂ C.N2).hom (C.σ ∘ c) := rfl

lemma g_d₁₂σ (c : cocycles₁ C.N3) : C.g.hom ∘ (d₁₂ C.N2).hom (C.σ ∘ c) = 0 := by
  rw [← d₁₂_comp]
  have : C.g.hom ∘ C.σ ∘ (c : Γ → C.N3) = c := funext fun s => C.hσ _
  rw [this]
  exact d₁₂_cocycles₁ c

lemma f_Δ₁ (c : cocycles₁ C.N3) : C.f.hom ∘ Δ₁ C c = (d₁₂ C.N2).hom (C.σ ∘ c) :=
  funext fun st => by rw [Δ₁_eq]; exact C.fπ (congrFun (g_d₁₂σ C c) st)

lemma Δ₁_mem_cocycles₂ (c : cocycles₁ C.N3) : Δ₁ C c ∈ cocycles₂ C.N1 := by
  show (d₂₃ C.N1).hom (Δ₁ C c) = 0
  apply comp_injective C.f C.hφ
  rw [← d₂₃_comp, f_Δ₁, d₂₃_d₁₂]
  funext x
  exact (map_zero C.f.hom).symm

lemma Δ₁_lcS₂ (c : cocycles₁ C.N3) (hc : IsLevelConstantS₁ S (c : Γ → C.N3)) : IsLevelConstantS₂ S (Δ₁ C c) := by
  obtain ⟨F, hF, h⟩ := hc
  refine ⟨F ⊔ C.L, hF.sup C.hLS, fun s t u u' hu hu' => ?_⟩
  have huF : u ∈ F.fixingSubgroup := IntermediateField.fixingSubgroup_antitone le_sup_left hu
  have hu'F : u' ∈ F.fixingSubgroup := IntermediateField.fixingSubgroup_antitone le_sup_left hu'
  have huL : u ∈ C.L.fixingSubgroup := IntermediateField.fixingSubgroup_antitone le_sup_right hu
  simp only [Δ₁_eq, Function.comp_apply, d₁₂_hom_apply]
  have e1 : s * u * (t * u') = s * u * t * u' := by group
  have key : c (s * u * t) = c (s * t) := by
    rw [(mem_cocycles₁_iff (c : Γ → C.N3)).1 c.2 (s * u) t, (mem_cocycles₁_iff (c : Γ → C.N3)).1 c.2 s t,
      h s u huF, map_mul, Module.End.mul_apply, C.hL3 u huL, Module.End.one_apply]
  rw [e1, h (s * u * t) u' hu'F, key, h t u' hu'F, h s u huF, map_mul, Module.End.mul_apply, C.hL2 u huL,
    Module.End.one_apply]

noncomputable def Δ₁z : levelCocyclesS₁ S C.N3 →ₗ[k] levelCocyclesS₂ S C.N1 :=
  (Δ₁ C ∘ₗ (levelCocyclesS₁ S C.N3).subtype).codRestrict _ fun c =>
    ⟨Δ₁_mem_cocycles₂ C c, Δ₁_lcS₂ C c c.2⟩

lemma coe_Δ₁z (c : levelCocyclesS₁ S C.N3) : (Δ₁z C c : Γ × Γ → C.N1) = Δ₁ C c := rfl

noncomputable def Δbar : levelCocyclesS₁ S C.N3 →ₗ[k] continuousH2S S C.N1 := continuousH2Sπ S C.N1 ∘ₗ Δ₁z C

lemma Δbar_apply (c : levelCocyclesS₁ S C.N3) : Δbar C c = continuousH2Sπ S C.N1 (Δ₁z C c) := rfl

lemma key (c : cocycles₁ C.N3) (b : Γ → C.N2) (hb : IsLevelConstantS₁ S b) (hbc : ∀ s, C.g.hom (b s) = c s) :
    C.π ∘ (d₁₂ C.N2).hom b - Δ₁ C c ∈ levelCoboundariesS₂ S C.N1 := by
  have hc : IsLevelConstantS₁ S (c : Γ → C.N3) := by
    have : (c : Γ → C.N3) = C.g.hom ∘ b := funext fun s => (hbc s).symm
    rw [this]; exact hb.comp _
  have hfa : C.f.hom ∘ (C.π ∘ (b - C.σ ∘ c)) = b - C.σ ∘ c := funext fun s => C.fπ (by
    rw [Pi.sub_apply, map_sub, hbc, Function.comp_apply, C.hσ, sub_self])
  refine (mem_levelCoboundariesS₂_iff S _ _).2 ⟨C.π ∘ (b - C.σ ∘ c), (lcS₁_sub hb (hc.comp _)).comp _, ?_⟩
  have hd : (d₁₂ C.N1).hom (C.π ∘ (b - C.σ ∘ c)) = C.π ∘ (d₁₂ C.N2).hom (b - C.σ ∘ c) := by
    conv_rhs => rw [← hfa, d₁₂_comp]
    funext st
    simp only [Function.comp_apply, C.hπ]
  rw [hd, map_sub]
  funext st
  simp only [Function.comp_apply, Pi.sub_apply, map_sub, Δ₁_eq]

lemma Δbar_eq_zero_of_πS_eq_zero (c : levelCocyclesS₁ S C.N3) (hc : πS S C.N3 c = 0) : Δbar C c = 0 := by
  have hc' : ((c : cocycles₁ C.N3) : Γ → C.N3) ∈ coboundaries₁ C.N3 := by
    rw [← H1π_hom_eq_zero_iff, ← coe_πS, hc, Submodule.coe_zero]
  obtain ⟨n, hn⟩ := hc'
  have hb : IsLevelConstantS₁ S ((d₀₁ C.N2).hom (C.σ n)) := lcS₁_d₀₁ C.hLS C.hL2 _
  have hbc : ∀ s, C.g.hom ((d₀₁ C.N2).hom (C.σ n) s) = (c : cocycles₁ C.N3) s := fun s => by
    rw [d₀₁_hom_apply, map_sub, Rep.hom_comm_apply, C.hσ, ← hn, d₀₁_hom_apply]
  have k1 := key C c _ hb hbc
  rw [d₁₂_d₀₁] at k1
  have h0 : C.π ∘ (0 : Γ × Γ → C.N2) = 0 := funext fun _ => map_zero C.π
  rw [h0, zero_sub] at k1
  rw [Δbar_apply, continuousH2Sπ_eq_zero_iff, coe_Δ₁z]
  simpa using neg_mem k1

noncomputable def delta₁Fun (y : continuousH1S S C.N3) : continuousH2S S C.N1 :=
  Δbar C (πS_surjective S C.N3 y).choose

lemma delta₁Fun_πS (c : levelCocyclesS₁ S C.N3) : delta₁Fun C (πS S C.N3 c) = Δbar C c := by
  have h := (πS_surjective S C.N3 (πS S C.N3 c)).choose_spec
  rw [delta₁Fun, ← sub_eq_zero, ← map_sub]
  exact Δbar_eq_zero_of_πS_eq_zero C _ (by rw [map_sub, h, sub_self])

noncomputable def delta₁ : continuousH1S S C.N3 →ₗ[k] continuousH2S S C.N1 where
  toFun := delta₁Fun C
  map_add' y y' := by
    obtain ⟨c, rfl⟩ := πS_surjective S C.N3 y
    obtain ⟨c', rfl⟩ := πS_surjective S C.N3 y'
    rw [← map_add, delta₁Fun_πS, delta₁Fun_πS, delta₁Fun_πS, map_add]
  map_smul' t y := by
    obtain ⟨c, rfl⟩ := πS_surjective S C.N3 y
    rw [← map_smul, delta₁Fun_πS, delta₁Fun_πS, map_smul, RingHom.id_apply]

lemma delta₁_πS (c : levelCocyclesS₁ S C.N3) : delta₁ C (πS S C.N3 c) = Δbar C c := delta₁Fun_πS C c

lemma delta₁_pin (x : continuousH1S S C.N3) (c : cocycles₁ C.N3) (b : Γ → C.N2) (e : levelCocyclesS₂ S C.N1)
    (hcx : (H1π C.N3).hom c = (x : H1 C.N3)) (hbc : ∀ s, C.g.hom (b s) = c s) (hb : IsLevelConstantS₁ S b)
    (he : ∀ s t, C.f.hom ((e : Γ × Γ → C.N1) (s, t)) = C.N2.ρ s (b t) - b (s * t) + b s) :
    delta₁ C x = continuousH2Sπ S C.N1 e := by
  have hc : IsLevelConstantS₁ S (c : Γ → C.N3) := by
    have : (c : Γ → C.N3) = C.g.hom ∘ b := funext fun s => (hbc s).symm
    rw [this]; exact hb.comp _
  have hx : x = πS S C.N3 ⟨c, hc⟩ := Subtype.ext hcx.symm
  rw [hx, delta₁_πS, Δbar_apply]
  have he' : (e : Γ × Γ → C.N1) = C.π ∘ (d₁₂ C.N2).hom b := funext fun ⟨s, t⟩ => by
    rw [Function.comp_apply, d₁₂_hom_apply, ← he, C.hπ]
  rw [← sub_eq_zero, ← map_sub, continuousH2Sπ_eq_zero_iff, Submodule.coe_sub, coe_Δ₁z, he']
  simpa using neg_mem (key C c b hb hbc)

end ctx

section exactness

variable {k : Type} [Field k] {S : Finset Nat.Primes} (C : Ctx k S)

lemma inj_i₀ : Function.Injective (i₀ C) := fun _ _ h => Subtype.ext (C.hφ (congrArg Subtype.val h))

lemma exact_i₀_p₀ : Function.Exact (i₀ C) (p₀ C) := by
  intro y
  constructor
  · intro hy
    have hy' : C.g.hom y = 0 := congrArg Subtype.val hy
    obtain ⟨a, ha⟩ := (C.hex _).1 hy'
    refine ⟨⟨a, fun γ => C.hφ ?_⟩, Subtype.ext ha⟩
    rw [Rep.hom_comm_apply, ha, y.2 γ]
  · rintro ⟨x, rfl⟩
    exact Subtype.ext (C.gf x)

lemma exact_p₀_delta₀ : Function.Exact (p₀ C) (delta₀ C) := by
  intro x
  constructor
  · intro hx
    have h0 : (delta₀ C x : H1 C.N1) = 0 := by rw [hx]; rfl
    rw [coe_delta₀, H1π_hom_eq_zero_iff, coe_δ₀z] at h0
    obtain ⟨a, ha⟩ := h0
    refine ⟨⟨C.σ x - C.f.hom a, fun γ => ?_⟩, Subtype.ext ?_⟩
    · have h1 := congrFun ha γ
      rw [d₀₁_hom_apply] at h1
      have h2 := congrArg C.f.hom h1
      rw [map_sub, Rep.hom_comm_apply, f_δ₀c C x.2] at h2
      rw [map_sub, sub_eq_sub_iff_sub_eq_sub]
      exact h2.symm
    · show C.g.hom (C.σ x - C.f.hom a) = x
      rw [map_sub, C.hσ, C.gf, sub_zero]
  · rintro ⟨y, rfl⟩
    apply Subtype.ext
    rw [delta₀_pin C (p₀ C y) y 0 rfl fun s => ?_, map_zero, Submodule.coe_zero]
    show C.f.hom 0 = _
    rw [map_zero, y.2 s, sub_self]

lemma exact_delta₀_i₁ : Function.Exact (delta₀ C) (mapH1S S C.f) := by
  intro x
  obtain ⟨a, ha, hax⟩ := exists_repS S x
  rw [← Submodule.coe_eq_zero, coe_mapH1S, ← hax, map_hom_H1π_hom, H1π_hom_eq_zero_iff, coe_mapCocycles₁_id]
  constructor
  · rintro ⟨y, hy⟩
    have hz : C.g.hom y ∈ C.N3.ρ.invariants := fun γ => by
      rw [← Rep.hom_comm_apply, ← sub_eq_zero, ← map_sub, ← d₀₁_hom_apply C.N2 y γ, hy, Function.comp_apply, C.gf]
    refine ⟨⟨C.g.hom y, hz⟩, Subtype.ext ?_⟩
    rw [← hax]
    refine delta₀_pin C ⟨_, hz⟩ y a rfl fun s => ?_
    have h1 := congrFun hy s
    rw [d₀₁_hom_apply] at h1
    exact h1.symm
  · rintro ⟨z, hz⟩
    have h1 := congrArg Subtype.val hz
    rw [coe_delta₀, ← hax, H1π_hom_eq_iff, coe_δ₀z] at h1
    obtain ⟨a₁, ha₁⟩ := h1
    refine ⟨C.σ z - C.f.hom a₁, ?_⟩
    rw [map_sub, d₀₁_comp, ha₁, ← f_comp_δ₀c C z.2]
    funext s
    simp only [Pi.sub_apply, Function.comp_apply, map_sub, sub_sub_cancel]

lemma exact_i₁_p₁ : Function.Exact (mapH1S S C.f) (mapH1S S C.g) := by
  intro x
  obtain ⟨b, hb, hbx⟩ := exists_repS S x
  rw [← Submodule.coe_eq_zero, coe_mapH1S, ← hbx, map_hom_H1π_hom, H1π_hom_eq_zero_iff, coe_mapCocycles₁_id]
  constructor
  · rintro ⟨n, hn⟩
    set b' : Γ → C.N2 := (b : Γ → C.N2) - (d₀₁ C.N2).hom (C.σ n) with hb'_def
    have hgb' : ∀ s, C.g.hom (b' s) = 0 := fun s => by
      have h1 := congrFun hn s
      rw [Function.comp_apply] at h1
      rw [hb'_def, Pi.sub_apply, map_sub, ← h1, d₀₁_hom_apply, d₀₁_hom_apply, map_sub, Rep.hom_comm_apply, C.hσ,
        sub_self]
    have hfa : C.f.hom ∘ (C.π ∘ b') = b' := funext fun s => C.fπ (hgb' s)
    have ha_coc : C.π ∘ b' ∈ cocycles₁ C.N1 := by
      show (d₁₂ C.N1).hom (C.π ∘ b') = 0
      apply comp_injective C.f C.hφ
      rw [← d₁₂_comp, hfa, hb'_def, map_sub, d₁₂_cocycles₁, d₁₂_d₀₁, sub_zero]
      funext st
      exact (map_zero C.f.hom).symm
    have ha_lc : IsLevelConstantS₁ S (C.π ∘ b') := (lcS₁_sub hb (lcS₁_d₀₁ C.hLS C.hL2 _)).comp _
    refine ⟨⟨(H1π C.N1).hom ⟨_, ha_coc⟩, (mem_continuousH1S_iff S _ _).2 ⟨_, ha_lc, rfl⟩⟩, Subtype.ext ?_⟩
    rw [coe_mapH1S, Submodule.coe_mk, map_hom_H1π_hom, ← hbx, H1π_hom_eq_iff, coe_mapCocycles₁_id]
    refine ⟨-C.σ n, ?_⟩
    rw [map_neg]
    change _ = C.f.hom ∘ (C.π ∘ b') - _
    rw [hfa, hb'_def]
    abel
  · rintro ⟨y, hyx⟩
    obtain ⟨a, ha, hay⟩ := exists_repS S y
    have h1 := congrArg Subtype.val hyx
    rw [coe_mapH1S, ← hay, map_hom_H1π_hom, ← hbx, H1π_hom_eq_iff, coe_mapCocycles₁_id] at h1
    obtain ⟨m, hm⟩ := h1
    refine ⟨-C.g.hom m, ?_⟩
    rw [map_neg, d₀₁_comp, hm]
    funext s
    simp only [Pi.neg_apply, Function.comp_apply, Pi.sub_apply, map_sub, C.gf, zero_sub, neg_neg]

lemma exact_p₁_delta₁ : Function.Exact (mapH1S S C.g) (delta₁ C) := by
  intro y
  obtain ⟨c, rfl⟩ := πS_surjective S C.N3 y
  rw [delta₁_πS, Δbar_apply, continuousH2Sπ_eq_zero_iff, coe_Δ₁z]
  constructor
  · intro h
    obtain ⟨a₁, ha₁, hda⟩ := (mem_levelCoboundariesS₂_iff S _ _).1 h
    set b : Γ → C.N2 := C.σ ∘ ((c : cocycles₁ C.N3) : Γ → C.N3) - C.f.hom ∘ a₁ with hb_def
    have hb_coc : b ∈ cocycles₁ C.N2 := by
      show (d₁₂ C.N2).hom b = 0
      rw [hb_def, map_sub, d₁₂_comp, hda, ← f_Δ₁, sub_self]
    have hb_lc : IsLevelConstantS₁ S b := lcS₁_sub (c.2.comp _) (ha₁.comp _)
    have hgb : C.g.hom ∘ b = ((c : cocycles₁ C.N3) : Γ → C.N3) := funext fun s => by
      simp only [hb_def, Pi.sub_apply, Function.comp_apply, map_sub, C.hσ, C.gf, sub_zero]
    refine ⟨⟨(H1π C.N2).hom ⟨b, hb_coc⟩, (mem_continuousH1S_iff S _ _).2 ⟨_, hb_lc, rfl⟩⟩, Subtype.ext ?_⟩
    rw [coe_mapH1S, Submodule.coe_mk, map_hom_H1π_hom, coe_πS]
    congr 1
    exact Subtype.ext hgb
  · rintro ⟨x, hx⟩
    obtain ⟨b, hb, hbx⟩ := exists_repS S x
    have h1 := congrArg Subtype.val hx
    rw [coe_mapH1S, ← hbx, map_hom_H1π_hom, coe_πS, H1π_hom_eq_iff, coe_mapCocycles₁_id] at h1
    have hc'lc : IsLevelConstantS₁ S ((mapCocycles₁ (MonoidHom.id Γ) C.g b : cocycles₁ C.N3) : Γ → C.N3) := by
      rw [coe_mapCocycles₁_id]; exact hb.comp _
    have hmem : mapCocycles₁ (MonoidHom.id Γ) C.g b ∈ levelCocyclesS₁ S C.N3 := hc'lc
    let c' : levelCocyclesS₁ S C.N3 := ⟨_, hmem⟩
    have hdiff : πS S C.N3 c' = πS S C.N3 c := by
      apply Subtype.ext
      rw [coe_πS, coe_πS]
      exact (H1π_hom_eq_iff _ _).2 h1
    have h2 : Δbar C c' = Δbar C c := by
      rw [← sub_eq_zero, ← map_sub]
      exact Δbar_eq_zero_of_πS_eq_zero C _ (by rw [map_sub, hdiff, sub_self])
    rw [Δbar_apply, Δbar_apply, ← sub_eq_zero, ← map_sub, continuousH2Sπ_eq_zero_iff, Submodule.coe_sub, coe_Δ₁z,
      coe_Δ₁z] at h2
    have h3 : Δ₁ C (mapCocycles₁ (MonoidHom.id Γ) C.g b) ∈ levelCoboundariesS₂ S C.N1 := by
      have k1 := key C (mapCocycles₁ (MonoidHom.id Γ) C.g b) b hb (fun s => rfl)
      rw [d₁₂_cocycles₁] at k1
      have h0 : C.π ∘ (0 : Γ × Γ → C.N2) = 0 := funext fun _ => map_zero C.π
      rw [h0, zero_sub] at k1
      simpa using neg_mem k1
    have h4 := sub_mem h3 h2
    change Δ₁ C (c' : cocycles₁ C.N3) - (Δ₁ C (c' : cocycles₁ C.N3) - Δ₁ C c) ∈ _ at h4
    rwa [sub_sub_cancel] at h4

lemma exact_delta₁_i₂ : Function.Exact (delta₁ C) (mapH2S S C.f) := by
  intro z
  induction z using Submodule.Quotient.induction_on with | _ e =>
  show mapH2S S C.f (continuousH2Sπ S C.N1 e) = 0 ↔ _
  rw [mapH2S_π, continuousH2Sπ_eq_zero_iff, coe_mapZ2S]
  constructor
  · intro h
    obtain ⟨b, hb, hdb⟩ := (mem_levelCoboundariesS₂_iff S _ _).1 h
    have hc_coc : C.g.hom ∘ b ∈ cocycles₁ C.N3 := by
      show (d₁₂ C.N3).hom (C.g.hom ∘ b) = 0
      rw [d₁₂_comp, hdb]
      funext st
      exact C.gf _
    have hc_lc : IsLevelConstantS₁ S (C.g.hom ∘ b) := hb.comp _
    let c' : levelCocyclesS₁ S C.N3 := ⟨⟨_, hc_coc⟩, hc_lc⟩
    refine ⟨πS S C.N3 c', ?_⟩
    rw [delta₁_πS, Δbar_apply]
    show continuousH2Sπ S C.N1 (Δ₁z C c') = continuousH2Sπ S C.N1 e
    rw [← sub_eq_zero, ← map_sub, continuousH2Sπ_eq_zero_iff, Submodule.coe_sub, coe_Δ₁z]
    have k1 := key C ⟨_, hc_coc⟩ b hb (fun s => rfl)
    rw [hdb] at k1
    have he : C.π ∘ (C.f.hom ∘ (e : Γ × Γ → C.N1)) = e := funext fun st => C.hπ _
    rw [he] at k1
    simpa using neg_mem k1
  · rintro ⟨y, hy⟩
    obtain ⟨c, rfl⟩ := πS_surjective S C.N3 y
    change delta₁ C (πS S C.N3 c) = continuousH2Sπ S C.N1 e at hy
    rw [delta₁_πS, Δbar_apply, ← sub_eq_zero, ← map_sub, continuousH2Sπ_eq_zero_iff, Submodule.coe_sub,
      coe_Δ₁z] at hy
    obtain ⟨a, ha, hda⟩ := (mem_levelCoboundariesS₂_iff S _ _).1 hy
    refine (mem_levelCoboundariesS₂_iff S _ _).2
      ⟨C.σ ∘ ((c : cocycles₁ C.N3) : Γ → C.N3) - C.f.hom ∘ a, lcS₁_sub (c.2.comp _) (ha.comp _), ?_⟩
    rw [map_sub, d₁₂_comp, hda, ← f_Δ₁]
    funext st
    simp only [Pi.sub_apply, Function.comp_apply, map_sub, sub_sub_cancel]

lemma exact_i₂_p₂ : Function.Exact (mapH2S S C.f) (mapH2S S C.g) := by
  intro z
  induction z using Submodule.Quotient.induction_on with | _ w =>
  show mapH2S S C.g (continuousH2Sπ S C.N2 w) = 0 ↔ _
  rw [mapH2S_π, continuousH2Sπ_eq_zero_iff, coe_mapZ2S]
  constructor
  · intro h
    obtain ⟨b₃, hb₃, hdb⟩ := (mem_levelCoboundariesS₂_iff S _ _).1 h
    set w' : Γ × Γ → C.N2 := (w : Γ × Γ → C.N2) - (d₁₂ C.N2).hom (C.σ ∘ b₃) with hw'_def
    have hgσ : C.g.hom ∘ (C.σ ∘ b₃) = b₃ := funext fun s => C.hσ _
    have hgw' : C.g.hom ∘ w' = 0 := by
      have e2 : C.g.hom ∘ w' = C.g.hom ∘ (w : Γ × Γ → C.N2) - C.g.hom ∘ (d₁₂ C.N2).hom (C.σ ∘ b₃) := by
        rw [hw'_def]; funext st; simp only [Function.comp_apply, Pi.sub_apply, map_sub]
      rw [e2, ← d₁₂_comp, hgσ, hdb, sub_self]
    have hfe : C.f.hom ∘ (C.π ∘ w') = w' := funext fun st => C.fπ (congrFun hgw' st)
    have he_coc : C.π ∘ w' ∈ cocycles₂ C.N1 := by
      show (d₂₃ C.N1).hom (C.π ∘ w') = 0
      apply comp_injective C.f C.hφ
      rw [← d₂₃_comp, hfe, hw'_def, map_sub, d₂₃_of_mem_cocycles₂ w.2.1, d₂₃_d₁₂, sub_zero]
      funext st
      exact (map_zero C.f.hom).symm
    have he_lc : IsLevelConstantS₂ S (C.π ∘ w') :=
      (lcS₂_sub w.2.2 (lcS₂_d₁₂ C.hLS C.hL2 (hb₃.comp _))).comp _
    refine ⟨continuousH2Sπ S C.N1 ⟨_, he_coc, he_lc⟩, ?_⟩
    show mapH2S S C.f (continuousH2Sπ S C.N1 ⟨_, he_coc, he_lc⟩) = continuousH2Sπ S C.N2 w
    rw [mapH2S_π, ← sub_eq_zero, ← map_sub, continuousH2Sπ_eq_zero_iff, Submodule.coe_sub, coe_mapZ2S]
    change C.f.hom ∘ (C.π ∘ w') - (w : Γ × Γ → C.N2) ∈ _
    rw [hfe, hw'_def]
    refine (mem_levelCoboundariesS₂_iff S _ _).2 ⟨-(C.σ ∘ b₃), (hb₃.comp C.σ).comp (fun v => -v), ?_⟩
    rw [map_neg]
    abel
  · rintro ⟨u, hu⟩
    induction u using Submodule.Quotient.induction_on with | _ e =>
    change mapH2S S C.f (continuousH2Sπ S C.N1 e) = continuousH2Sπ S C.N2 w at hu
    rw [mapH2S_π, ← sub_eq_zero, ← map_sub, continuousH2Sπ_eq_zero_iff, Submodule.coe_sub, coe_mapZ2S] at hu
    obtain ⟨b₂, hb₂, hdb₂⟩ := (mem_levelCoboundariesS₂_iff S _ _).1 hu
    refine (mem_levelCoboundariesS₂_iff S _ _).2 ⟨-(C.g.hom ∘ b₂), (hb₂.comp _).comp (fun v => -v), ?_⟩
    rw [map_neg, d₁₂_comp, hdb₂]
    funext st
    simp only [Pi.neg_apply, Function.comp_apply, Pi.sub_apply, map_sub, C.gf, zero_sub, neg_neg]

end exactness

end P2mS25LES8

open P2mS25LES8 in
set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (N1 N2 N3 : Rep.{0} (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    [FiniteDimensional (ZMod p) N1] [FiniteDimensional (ZMod p) N2] [FiniteDimensional (ZMod p) N3]
    (f : N1 ⟶ N2) (g : N2 ⟶ N3) (hfg : f ≫ g = 0)
    (hex : (ShortComplex.mk f g hfg).ShortExact)
    (hsm : ∀ m : N2, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s ∈ F.fixingSubgroup, N2.ρ s m = m)
    (hur : ∀ q : Nat.Primes, q ∉ S → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
      A.LiesOverPrime (q : ℕ) → ∀ s ∈ A.inertiaSubgroupIn ℚ, N2.ρ s = 1) :
    ∃ (i₀ : N1.ρ.invariants →ₗ[ZMod p] N2.ρ.invariants) (p₀ : N2.ρ.invariants →ₗ[ZMod p] N3.ρ.invariants)
      (δ₀ : N3.ρ.invariants →ₗ[ZMod p] ↥(continuousH1S S N1))
      (i₁ : ↥(continuousH1S S N1) →ₗ[ZMod p] ↥(continuousH1S S N2))
      (p₁ : ↥(continuousH1S S N2) →ₗ[ZMod p] ↥(continuousH1S S N3))
      (δ₁ : ↥(continuousH1S S N3) →ₗ[ZMod p] continuousH2S S N1)
      (i₂ : continuousH2S S N1 →ₗ[ZMod p] continuousH2S S N2)
      (p₂ : continuousH2S S N2 →ₗ[ZMod p] continuousH2S S N3),

      (∀ x, (i₀ x : N2) = f.hom x) ∧ (∀ y, (p₀ y : N3) = g.hom y) ∧
      (∀ x, (i₁ x : H1 N2) = (map (MonoidHom.id _) f 1).hom x) ∧
      (∀ y, (p₁ y : H1 N3) = (map (MonoidHom.id _) g 1).hom y) ∧

      (∀ (x : N3.ρ.invariants) (y : N2) (c : cocycles₁ N1), g.hom y = (x : N3) →
          (∀ s, f.hom (c s) = N2.ρ s y - y) → (δ₀ x : H1 N1) = (H1π N1).hom c) ∧

      (∀ (z : levelCocyclesS₂ S N1) (z' : levelCocyclesS₂ S N2),
          (∀ st, (z' : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) × (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → N2) st = f.hom ((z : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) × (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → N1) st)) → i₂ (continuousH2Sπ S N1 z) = continuousH2Sπ S N2 z') ∧
      (∀ (z : levelCocyclesS₂ S N2) (z' : levelCocyclesS₂ S N3),
          (∀ st, (z' : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) × (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → N3) st = g.hom ((z : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) × (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → N2) st)) → p₂ (continuousH2Sπ S N2 z) = continuousH2Sπ S N3 z') ∧

      (∀ (x : ↥(continuousH1S S N3)) (c : cocycles₁ N3) (b : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → N2) (e : levelCocyclesS₂ S N1),
          (H1π N3).hom c = (x : H1 N3) → (∀ s, g.hom (b s) = c s) → IsLevelConstantS₁ S b →
          (∀ s t, f.hom ((e : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) × (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → N1) (s, t)) = N2.ρ s (b t) - b (s * t) + b s) →
          δ₁ x = continuousH2Sπ S N1 e) ∧

      Function.Injective i₀ ∧ Function.Exact i₀ p₀ ∧ Function.Exact p₀ δ₀ ∧ Function.Exact δ₀ i₁ ∧
      Function.Exact i₁ p₁ ∧ Function.Exact p₁ δ₁ ∧ Function.Exact δ₁ i₂ ∧ Function.Exact i₂ p₂ := by
  have hinjf : Function.Injective f.hom := (Rep.mono_iff_injective f).1 hex.mono_f
  have hsurg : Function.Surjective g.hom := (Rep.epi_iff_surjective g).1 hex.epi_g
  have hM := hex.map_of_exact (forget₂ (Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (ModuleCat (ZMod p)))
  have hrk : LinearMap.range f.hom.toLinearMap = LinearMap.ker g.hom.toLinearMap := hM.exact.moduleCat_range_eq_ker
  have hex' : ∀ b : N2, g.hom b = 0 ↔ ∃ a : N1, f.hom a = b := fun b => by
    constructor
    · intro hb
      have hb' : b ∈ LinearMap.ker g.hom.toLinearMap := hb
      rw [← hrk] at hb'
      obtain ⟨a, ha⟩ := hb'
      exact ⟨a, ha⟩
    · rintro ⟨a, rfl⟩
      have ha : f.hom.toLinearMap a ∈ LinearMap.range f.hom.toLinearMap := ⟨a, rfl⟩
      rw [hrk] at ha
      exact ha
  obtain ⟨σl, hσl⟩ := LinearMap.exists_rightInverse_of_surjective g.hom.toLinearMap (LinearMap.range_eq_top.2 hsurg)
  obtain ⟨πl, hπl⟩ := LinearMap.exists_leftInverse_of_injective f.hom.toLinearMap (LinearMap.ker_eq_bot.2 hinjf)
  obtain ⟨L, hLS, hL2⟩ := groupCohomology.exists_isUnramifiedOutside_forall_apply_eq_one_of_smooth S N2 hsm hur
  let C : Ctx (ZMod p) S :=
    { N1 := N1, N2 := N2, N3 := N3, f := f, g := g, hφ := hinjf, hex := hex', σ := σl,
      hσ := fun x => LinearMap.congr_fun hσl x, π := πl, hπ := fun a => LinearMap.congr_fun hπl a,
      L := L, hLS := hLS, hL2 := hL2 }
  refine ⟨i₀ C, p₀ C, delta₀ C, mapH1S S f, mapH1S S g, delta₁ C, mapH2S S f, mapH2S S g,
    fun x => rfl, fun y => rfl, fun x => rfl, fun y => rfl,
    fun x y c hy hc => delta₀_pin C x y c hy hc,
    fun z z' h => mapH2S_pin S f z z' h, fun z z' h => mapH2S_pin S g z z' h,
    fun x c b e hcx hbc hb he => delta₁_pin C x c b e hcx hbc hb he,
    inj_i₀ C, exact_i₀_p₀ C, exact_p₀_delta₀ C, exact_delta₀_i₁ C, exact_i₁_p₁ C, exact_p₁_delta₁ C,
    exact_delta₁_i₂ C, exact_i₂_p₂ C⟩

end S_groupCohomology_exists_les_continuousHS_of_shortExact_of_isLevelConstant
end P2MW
export P2MW.S_groupCohomology_exists_les_continuousHS_of_shortExact_of_isLevelConstant (solution)
