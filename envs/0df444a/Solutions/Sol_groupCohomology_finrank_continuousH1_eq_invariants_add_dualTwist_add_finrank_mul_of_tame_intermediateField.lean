-- Prove2me | solution 1 for groupCohomology.finrank_continuousH1_eq_invariants_add_dualTwist_add_finrank_mul_of_tame_intermediateField
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/11d7e78d-e313-5ca4-8a72-592d60a1231d

import Mathlib
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GroupCohomology_ContinuousH1
import Theorems.Thm_localGaloisToGlobal_mem_fixingSubgroup_iff
import Theorems.Thm_IntermediateField_exists_le_adjoin_padicEmbedding_image
import Theorems.Thm_exists_finiteDimensional_comap_localGaloisToGlobal_iff
import Theorems.Thm_ExtCitation_exists_isPrimitiveRoot_smul_eq_pow_cycloChar_localGaloisToGlobal
import Theorems.Thm_groupCohomology_finrank_continuousClasses_eq_finrank_of_isUnit_index_of_forall_apply_eq
import Theorems.Thm_Representation_finrank_invariants_linHom_dual_twist_ofChar
import Theorems.Thm_Representation_finrank_invariants_dual_of_isUnit_card
import Theorems.Thm_ExtCitation_LocalLevel_finrank_invariants_linHom_unitsModPow_of_isGalois_intermediateField
import Theorems.Thm_groupCohomology_finrank_continuousEquivariantHom_eq_finrank_invariants_linHom_dualTwist
import Definitions.Def_P2M_Util
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_finrank_continuousH1_eq_invariants_add_dualTwist_add_finrank_mul_of_tame_intermediateField
p2m_attr_erase "instance" "groupCohomology.Kummer.instMulDistribMulActionRootsOfUnity"
p2m_attr_erase "simp" "groupCohomology.Kummer.coe_kummerCocycleRoots groupCohomology.Kummer.mem_powerSubgroup_iff groupCohomology.Kummer.val_smul_units groupCohomology.Kummer.kummerHom_apply groupCohomology.Kummer.coe_smul_rootsOfUnity"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
open CategoryTheory Module groupCohomology ExtCitation
open scoped IntermediateField Pointwise

namespace PDevissage

section Basic
variable (A : Type*) [AddCommGroup A] (p : ℕ)

private def tor : AddSubgroup A := (DistribSMul.toAddMonoidHom A p).ker

private def pmul : AddSubgroup A := (DistribSMul.toAddMonoidHom A p).range

variable {A p}

private theorem mem_tor {a : A} : a ∈ tor A p ↔ p • a = 0 := Iff.rfl
private theorem mem_pmul {a : A} : a ∈ pmul A p ↔ ∃ a', p • a' = a := Iff.rfl

private scoped instance torModule [Fact p.Prime] : Module (ZMod p) (tor A p) :=
  AddCommGroup.zmodModule (fun x => Subtype.ext (by
    rw [AddSubgroup.coe_nsmul, AddSubgroup.coe_zero]; exact mem_tor.mp x.2))

private scoped instance quotModule [Fact p.Prime] : Module (ZMod p) (A ⧸ pmul A p) :=
  AddCommGroup.zmodModule (by
    intro x
    induction x using QuotientAddGroup.induction_on with
    | H a => rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]; exact ⟨a, rfl⟩)

end Basic

section Functorial
variable {A B : Type*} [AddCommGroup A] [AddCommGroup B] {p : ℕ} [Fact p.Prime]

private def torMap (f : A →+ B) : tor A p →ₗ[ZMod p] tor B p :=
  AddMonoidHom.toZModLinearMap p
    ((f.comp (tor A p).subtype).codRestrict (tor B p) (fun x => by
      rw [mem_tor, AddMonoidHom.comp_apply, ← map_nsmul, AddSubgroup.coe_subtype, ← AddSubgroup.coe_nsmul,
        show p • x = 0 from Subtype.ext (by rw [AddSubgroup.coe_nsmul, AddSubgroup.coe_zero]; exact mem_tor.mp x.2),
        AddSubgroup.coe_zero, map_zero]))

@[scoped simp] private theorem coe_torMap (f : A →+ B) (x : tor A p) : (torMap f x : B) = f x := rfl

private def quotMap (f : A →+ B) : (A ⧸ pmul A p) →ₗ[ZMod p] (B ⧸ pmul B p) :=
  AddMonoidHom.toZModLinearMap p
    (QuotientAddGroup.map (pmul A p) (pmul B p) f (by
      rintro _ ⟨a, rfl⟩; exact ⟨f a, by simp [map_nsmul]⟩))

@[scoped simp] private theorem quotMap_mk (f : A →+ B) (a : A) :
    quotMap (p := p) f (QuotientAddGroup.mk a) = QuotientAddGroup.mk (f a) := rfl

private theorem torMap_comp {C : Type*} [AddCommGroup C] (f : A →+ B) (g : B →+ C) :
    torMap (p := p) (g.comp f) = torMap g ∘ₗ torMap f := by
  ext x; rfl

private theorem quotMap_comp {C : Type*} [AddCommGroup C] (f : A →+ B) (g : B →+ C) :
    quotMap (p := p) (g.comp f) = quotMap g ∘ₗ quotMap f := by
  apply LinearMap.ext; intro x
  induction x using QuotientAddGroup.induction_on with
  | H a => rfl

private theorem torMap_id : torMap (p := p) (AddMonoidHom.id A) = LinearMap.id := by ext; rfl
private theorem quotMap_id : quotMap (p := p) (AddMonoidHom.id A) = LinearMap.id := by
  apply LinearMap.ext; intro x
  induction x using QuotientAddGroup.induction_on with
  | H a => rfl

end Functorial

section Action
variable {Δ : Type*} [Group Δ] {A : Type*} [AddCommGroup A] {p : ℕ} [Fact p.Prime]

private def torRep (act : Δ →* AddAut A) : Representation (ZMod p) Δ (tor A p) where
  toFun d := torMap ((act d : A ≃+ A) : A →+ A)
  map_one' := by ext x; simp
  map_mul' d d' := by ext x; simp

private def quotRep (act : Δ →* AddAut A) : Representation (ZMod p) Δ (A ⧸ pmul A p) where
  toFun d := quotMap ((act d : A ≃+ A) : A →+ A)
  map_one' := by
    apply LinearMap.ext; intro x
    induction x using QuotientAddGroup.induction_on with
    | H a => simp
  map_mul' d d' := by
    apply LinearMap.ext; intro x
    induction x using QuotientAddGroup.induction_on with
    | H a => simp

@[scoped simp] private theorem coe_torRep (act : Δ →* AddAut A) (d : Δ) (x : tor A p) : (torRep act d x : A) = act d x := rfl
@[scoped simp] private theorem quotRep_mk (act : Δ →* AddAut A) (d : Δ) (a : A) :
    quotRep (p := p) act d (QuotientAddGroup.mk a) = QuotientAddGroup.mk (act d a) := rfl

end Action

end PDevissage
p2m_reactivate "P2MW.S_groupCohomology_finrank_continuousH1_eq_invariants_add_dualTwist_add_finrank_mul_of_tame_intermediateField.PDevissage"

namespace PDevissage

section SubQuot
variable {Δ : Type*} [Group Δ] {A : Type*} [AddCommGroup A] {p : ℕ} [Fact p.Prime]
variable (act : Δ →* AddAut A) (B : AddSubgroup A) (hB : ∀ (d : Δ) (a : A), a ∈ B → act d a ∈ B)

private theorem act_inv_apply (d : Δ) (a : A) : act d⁻¹ (act d a) = a := by
  rw [← AddAut.mul_apply', ← map_mul, inv_mul_cancel, map_one, AddAut.one_apply']

private theorem act_apply_inv (d : Δ) (a : A) : act d (act d⁻¹ a) = a := by
  rw [← AddAut.mul_apply', ← map_mul, mul_inv_cancel, map_one, AddAut.one_apply']

include hB in
private theorem act_mem_iff (d : Δ) (a : A) : act d a ∈ B ↔ a ∈ B :=
  ⟨fun h => by simpa [act_inv_apply] using hB d⁻¹ _ h, hB d a⟩

private def subAct : Δ →* AddAut B where
  toFun d :=
    { toFun := fun b => ⟨act d b, hB d b b.2⟩
      invFun := fun b => ⟨act d⁻¹ b, hB d⁻¹ b b.2⟩
      left_inv := fun b => Subtype.ext (act_inv_apply act d b)
      right_inv := fun b => Subtype.ext (act_apply_inv act d b)
      map_add' := fun b b' => Subtype.ext (map_add _ _ _) }
  map_one' := by ext b; simp
  map_mul' d d' := by ext b; simp

@[scoped simp] private theorem coe_subAct (d : Δ) (b : B) : ((subAct act B hB d b : B) : A) = act d b := rfl

private def quotAct : Δ →* AddAut (A ⧸ B) where
  toFun d :=
    { toFun := QuotientAddGroup.map B B (act d : A ≃+ A) (fun a ha => hB d a ha)
      invFun := QuotientAddGroup.map B B (act d⁻¹ : A ≃+ A) (fun a ha => hB d⁻¹ a ha)
      left_inv := fun x => by
        induction x using QuotientAddGroup.induction_on with
        | H a => simp
      right_inv := fun x => by
        induction x using QuotientAddGroup.induction_on with
        | H a => simp
      map_add' := fun x y => map_add _ _ _ }
  map_one' := by
    ext x
    induction x using QuotientAddGroup.induction_on with
    | H a => simp
  map_mul' d d' := by
    ext x
    induction x using QuotientAddGroup.induction_on with
    | H a => simp

@[scoped simp] private theorem quotAct_mk (d : Δ) (a : A) :
    quotAct act B hB d (QuotientAddGroup.mk a) = QuotientAddGroup.mk (act d a) := rfl

end SubQuot
p2m_reactivate "P2MW.S_groupCohomology_finrank_continuousH1_eq_invariants_add_dualTwist_add_finrank_mul_of_tame_intermediateField.PDevissage"
end PDevissage
p2m_reactivate "P2MW.S_groupCohomology_finrank_continuousH1_eq_invariants_add_dualTwist_add_finrank_mul_of_tame_intermediateField.PDevissage"

namespace PDevissage

section Snake
variable {Δ : Type*} [Group Δ] {A : Type*} [AddCommGroup A] {p : ℕ} [Fact p.Prime]
variable (act : Δ →* AddAut A) (B : AddSubgroup A) (hB : ∀ (d : Δ) (a : A), a ∈ B → act d a ∈ B)

local notation "C" => A ⧸ B

private def Ti : tor B p →ₗ[ZMod p] tor A p := torMap B.subtype

private def Tq : tor A p →ₗ[ZMod p] tor C p := torMap (QuotientAddGroup.mk' B)

private def Qi : (B ⧸ pmul B p) →ₗ[ZMod p] (A ⧸ pmul A p) := quotMap B.subtype

private def Qq : (A ⧸ pmul A p) →ₗ[ZMod p] (C ⧸ pmul C p) := quotMap (QuotientAddGroup.mk' B)

private theorem nsmul_out_mem (c : tor C p) : p • Quotient.out (c : C) ∈ B := by
  rw [← QuotientAddGroup.eq_zero_iff, QuotientAddGroup.mk_nsmul, QuotientAddGroup.out_eq']
  exact_mod_cast mem_tor.mp c.2

private theorem nsmul_mem_of_mk_eq (c : tor C p) (a : A) (ha : (QuotientAddGroup.mk a : C) = c) : p • a ∈ B := by
  rw [← QuotientAddGroup.eq_zero_iff, QuotientAddGroup.mk_nsmul, ha]
  exact_mod_cast mem_tor.mp c.2

private noncomputable def delta₀ (c : tor C p) : B ⧸ pmul B p := QuotientAddGroup.mk ⟨p • Quotient.out (c : C), nsmul_out_mem B c⟩

private theorem delta₀_eq (c : tor C p) (a : A) (ha : (QuotientAddGroup.mk a : C) = c) :
    delta₀ B c = QuotientAddGroup.mk ⟨p • a, nsmul_mem_of_mk_eq B c a ha⟩ := by
  show QuotientAddGroup.mk _ = QuotientAddGroup.mk _
  rw [QuotientAddGroup.eq]

  have hdiff : -Quotient.out (c : C) + a ∈ B := by
    rw [← QuotientAddGroup.eq, QuotientAddGroup.out_eq', ha]
  refine ⟨⟨-Quotient.out (c : C) + a, hdiff⟩, Subtype.ext ?_⟩
  simp [smul_add]

private noncomputable def delta : tor C p →ₗ[ZMod p] (B ⧸ pmul B p) :=
  AddMonoidHom.toZModLinearMap p
    { toFun := delta₀ B
      map_zero' := by
        rw [delta₀_eq B (0 : tor C p) 0 (by simp), QuotientAddGroup.eq_zero_iff]
        exact ⟨0, Subtype.ext (by simp)⟩
      map_add' := fun c c' => by
        rw [delta₀_eq B (c + c') (Quotient.out (c : C) + Quotient.out (c' : C)) (by simp)]
        show _ = (QuotientAddGroup.mk _ : B ⧸ pmul B p) + QuotientAddGroup.mk _
        rw [← QuotientAddGroup.mk_add]
        congr 1
        apply Subtype.ext
        simp [smul_add] }

private theorem delta_apply (c : tor C p) (a : A) (ha : (QuotientAddGroup.mk a : C) = c) :
    delta B c = QuotientAddGroup.mk ⟨p • a, nsmul_mem_of_mk_eq B c a ha⟩ :=
  delta₀_eq B c a ha

private theorem Ti_injective : Function.Injective (Ti (p := p) B) := by
  intro x y h
  have h' : ((x : B) : A) = ((y : B) : A) := congrArg (fun z : tor A p => (z : A)) h
  exact Subtype.ext (Subtype.ext h')

private theorem exact_Ti_Tq : Function.Exact (Ti (p := p) B) (Tq (p := p) B) := by
  intro x
  constructor
  · intro hx

    have hx' : ((x : A) : C) = 0 := congrArg (fun z : tor C p => (z : C)) hx
    rw [QuotientAddGroup.eq_zero_iff] at hx'
    have hpx : p • (x : A) = 0 := mem_tor.mp x.2
    refine ⟨⟨⟨x, hx'⟩, mem_tor.mpr (Subtype.ext ?_)⟩, Subtype.ext rfl⟩
    push_cast
    exact hpx
  · rintro ⟨y, rfl⟩
    apply Subtype.ext
    show ((((y : B) : A)) : C) = 0
    rw [QuotientAddGroup.eq_zero_iff]
    exact (y : B).2

private theorem exact_Tq_delta : Function.Exact (Tq (p := p) B) (delta (p := p) B) := by
  intro c
  constructor
  · intro hc
    rw [delta_apply B c (Quotient.out (c : C)) (QuotientAddGroup.out_eq' _), QuotientAddGroup.eq_zero_iff] at hc
    obtain ⟨b, hb⟩ := hc

    have hb' : p • ((b : B) : A) = p • Quotient.out (c : C) := by
      have := congrArg (fun z : B => (z : A)) hb
      simpa using this
    refine ⟨⟨Quotient.out (c : C) - b, mem_tor.mpr ?_⟩, Subtype.ext ?_⟩
    · rw [smul_sub, ← hb', sub_self]
    · show (QuotientAddGroup.mk (Quotient.out (c : C) - (b : A)) : C) = c
      rw [QuotientAddGroup.mk_sub, QuotientAddGroup.out_eq', (QuotientAddGroup.eq_zero_iff _).mpr b.2, sub_zero]
  · rintro ⟨a, rfl⟩
    rw [delta_apply B _ (a : A) rfl, QuotientAddGroup.eq_zero_iff]
    refine ⟨0, Subtype.ext ?_⟩
    show ((p • (0 : B) : B) : A) = p • (a : A)
    rw [smul_zero, ZeroMemClass.coe_zero]
    exact (mem_tor.mp a.2).symm

private theorem exact_delta_Qi : Function.Exact (delta (p := p) B) (Qi (p := p) B) := by
  intro x
  constructor
  · intro hx
    induction x using QuotientAddGroup.induction_on with
    | H b =>

      change (QuotientAddGroup.mk ((b : B) : A) : A ⧸ pmul A p) = 0 at hx
      rw [QuotientAddGroup.eq_zero_iff] at hx
      obtain ⟨a, ha⟩ := hx
      change p • a = _ at ha
      have hc : p • (QuotientAddGroup.mk a : C) = 0 := by
        rw [← QuotientAddGroup.mk_nsmul, ha, QuotientAddGroup.eq_zero_iff]; exact b.2
      refine ⟨⟨QuotientAddGroup.mk a, mem_tor.mpr hc⟩, ?_⟩
      rw [delta_apply B _ a rfl]
      congr 1
      exact Subtype.ext ha
  · rintro ⟨c, rfl⟩
    rw [delta_apply B c (Quotient.out (c : C)) (QuotientAddGroup.out_eq' _)]
    change (QuotientAddGroup.mk (p • Quotient.out (c : C)) : A ⧸ pmul A p) = 0
    rw [QuotientAddGroup.eq_zero_iff]
    exact ⟨_, rfl⟩

private theorem exact_Qi_Qq : Function.Exact (Qi (p := p) B) (Qq (p := p) B) := by
  intro x
  constructor
  · intro hx
    induction x using QuotientAddGroup.induction_on with
    | H a =>
      change (QuotientAddGroup.mk (QuotientAddGroup.mk a : C) : C ⧸ pmul C p) = 0 at hx
      rw [QuotientAddGroup.eq_zero_iff] at hx
      obtain ⟨c', hc'⟩ := hx
      change p • c' = _ at hc'
      induction c' using QuotientAddGroup.induction_on with
      | H a' =>

        have hmem : a - p • a' ∈ B := by
          rw [← QuotientAddGroup.eq_zero_iff, QuotientAddGroup.mk_sub, QuotientAddGroup.mk_nsmul, hc', sub_self]
        refine ⟨QuotientAddGroup.mk ⟨a - p • a', hmem⟩, ?_⟩
        change (QuotientAddGroup.mk ((⟨a - p • a', hmem⟩ : B) : A) : A ⧸ pmul A p) = QuotientAddGroup.mk a
        rw [QuotientAddGroup.eq]
        exact ⟨a', by simp⟩
  · rintro ⟨y, rfl⟩
    induction y using QuotientAddGroup.induction_on with
    | H b =>
      change (QuotientAddGroup.mk (QuotientAddGroup.mk ((b : B) : A) : C) : C ⧸ pmul C p) = 0
      rw [(QuotientAddGroup.eq_zero_iff _).mpr b.2, QuotientAddGroup.mk_zero]

private theorem Qq_surjective : Function.Surjective (Qq (p := p) B) := by
  intro x
  induction x using QuotientAddGroup.induction_on with
  | H c =>
    induction c using QuotientAddGroup.induction_on with
    | H a => exact ⟨QuotientAddGroup.mk a, rfl⟩

end Snake
p2m_reactivate "P2MW.S_groupCohomology_finrank_continuousH1_eq_invariants_add_dualTwist_add_finrank_mul_of_tame_intermediateField.PDevissage"
end PDevissage
p2m_reactivate "P2MW.S_groupCohomology_finrank_continuousH1_eq_invariants_add_dualTwist_add_finrank_mul_of_tame_intermediateField.PDevissage"

namespace PDevissage

section HomExact
variable {k : Type*} [Field k] {Δ : Type*} [Group Δ]
variable {VN : Type*} [AddCommGroup VN] [Module k VN] (N : Representation k Δ VN)

private theorem mem_invariants_linHom_iff {VW : Type*} [AddCommGroup VW] [Module k VW] (W : Representation k Δ VW)
    (φ : VN →ₗ[k] VW) : φ ∈ (N.linHom W).invariants ↔ ∀ (d : Δ) (v : VN), φ (N d v) = W d (φ v) := by
  rw [Representation.mem_invariants]
  constructor
  · intro h d v
    have := LinearMap.congr_fun (h d) (N d v)
    simp only [Representation.linHom_apply, LinearMap.coe_comp, Function.comp_apply] at this
    rw [← this, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  · intro h d
    apply LinearMap.ext
    intro v
    simp only [Representation.linHom_apply, LinearMap.coe_comp, Function.comp_apply]
    rw [h, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

variable {VA VB VC : Type*} [AddCommGroup VA] [Module k VA] [AddCommGroup VB] [Module k VB]
  [AddCommGroup VC] [Module k VC]
  (PA : Representation k Δ VA) (PB : Representation k Δ VB) (PC : Representation k Δ VC)

private def postComp (f : VA →ₗ[k] VB) (hf : ∀ d, f ∘ₗ PA d = PB d ∘ₗ f) :
    (N.linHom PA).invariants →ₗ[k] (N.linHom PB).invariants where
  toFun φ := ⟨f ∘ₗ (φ : VN →ₗ[k] VA), by
    rw [mem_invariants_linHom_iff]
    intro d v
    rw [LinearMap.comp_apply, LinearMap.comp_apply, (mem_invariants_linHom_iff N PA _).mp φ.2 d v]
    exact LinearMap.congr_fun (hf d) _⟩
  map_add' _ _ := Subtype.ext (by simp [LinearMap.comp_add])
  map_smul' _ _ := Subtype.ext (by simp [LinearMap.comp_smul])

@[scoped simp] private theorem coe_postComp (f : VA →ₗ[k] VB) (hf : ∀ d, f ∘ₗ PA d = PB d ∘ₗ f) (φ : (N.linHom PA).invariants) :
    ((postComp N PA PB f hf φ : (N.linHom PB).invariants) : VN →ₗ[k] VB) = f ∘ₗ (φ : VN →ₗ[k] VA) := rfl

private theorem postComp_injective (f : VA →ₗ[k] VB) (hf : ∀ d, f ∘ₗ PA d = PB d ∘ₗ f) (hinj : Function.Injective f) :
    Function.Injective (postComp N PA PB f hf) := by
  intro φ φ' h
  apply Subtype.ext
  apply LinearMap.ext
  intro v
  apply hinj
  exact LinearMap.congr_fun (congrArg Subtype.val h) v

variable [Fintype Δ] [Invertible (Fintype.card Δ : k)]

private theorem exists_postComp_eq (f : VA →ₗ[k] VB) (hf : ∀ d, f ∘ₗ PA d = PB d ∘ₗ f)
    (φ : (N.linHom PB).invariants) (χ : VN →ₗ[k] VA) (hχ : f ∘ₗ χ = (φ : VN →ₗ[k] VB)) :
    ∃ ψ : (N.linHom PA).invariants, postComp N PA PB f hf ψ = φ := by
  classical
  refine ⟨⟨(N.linHom PA).averageMap χ, (N.linHom PA).averageMap_invariant χ⟩, Subtype.ext ?_⟩
  show f ∘ₗ (N.linHom PA).averageMap χ = (φ : VN →ₗ[k] VB)
  have hexp : (N.linHom PA).averageMap χ = ⅟(Fintype.card Δ : k) • ∑ d : Δ, (N.linHom PA) d χ := by
    simp [Representation.averageMap, GroupAlgebra.average, map_sum, LinearMap.sum_apply]
  have hterm : ∀ d : Δ, f ∘ₗ ((N.linHom PA) d χ) = (φ : VN →ₗ[k] VB) := by
    intro d
    apply LinearMap.ext
    intro v
    simp only [Representation.linHom_apply, LinearMap.coe_comp, Function.comp_apply]
    have hfx := LinearMap.congr_fun (hf d) (χ (N d⁻¹ v))
    simp only [LinearMap.coe_comp, Function.comp_apply] at hfx
    rw [hfx, show f (χ (N d⁻¹ v)) = (φ : VN →ₗ[k] VB) (N d⁻¹ v) from LinearMap.congr_fun hχ _,
      (mem_invariants_linHom_iff N PB _).mp φ.2 d⁻¹ v, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel,
      map_one, Module.End.one_apply]
  rw [hexp, LinearMap.comp_smul]
  have hsum : f ∘ₗ (∑ d : Δ, (N.linHom PA) d χ) = ∑ d : Δ, f ∘ₗ ((N.linHom PA) d χ) := by
    apply LinearMap.ext; intro v; simp [LinearMap.sum_apply, map_sum]
  rw [hsum]
  simp only [hterm, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul k, smul_smul, invOf_mul_self, one_smul]

private theorem postComp_surjective (g : VB →ₗ[k] VC) (hg : ∀ d, g ∘ₗ PB d = PC d ∘ₗ g) (hsurj : Function.Surjective g) :
    Function.Surjective (postComp N PB PC g hg) := by
  intro φ
  obtain ⟨s, hs⟩ := g.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hsurj)
  exact exists_postComp_eq N PB PC g hg φ (s ∘ₗ (φ : VN →ₗ[k] VC))
    (by rw [← LinearMap.comp_assoc, hs, LinearMap.id_comp])

private theorem exact_postComp (f : VA →ₗ[k] VB) (hf : ∀ d, f ∘ₗ PA d = PB d ∘ₗ f)
    (g : VB →ₗ[k] VC) (hg : ∀ d, g ∘ₗ PB d = PC d ∘ₗ g) (hexact : Function.Exact f g) :
    Function.Exact (postComp N PA PB f hf) (postComp N PB PC g hg) := by
  intro φ
  constructor
  · intro hφ

    have hφ0 : ∀ v, g ((φ : VN →ₗ[k] VB) v) = 0 := fun v =>
      LinearMap.congr_fun (congrArg Subtype.val hφ) v
    have hrange : LinearMap.range (φ : VN →ₗ[k] VB) ≤ LinearMap.range f := by
      rintro _ ⟨v, rfl⟩
      exact (hexact _).mp (hφ0 v)
    obtain ⟨χ, hχ⟩ := Module.projective_lifting_property f.rangeRestrict
      ((φ : VN →ₗ[k] VB).codRestrict (LinearMap.range f) (fun v => hrange ⟨v, rfl⟩))
      (LinearMap.surjective_rangeRestrict f)
    have hχ' : f ∘ₗ χ = (φ : VN →ₗ[k] VB) := by
      apply LinearMap.ext; intro v
      exact congrArg Subtype.val (LinearMap.congr_fun hχ v)
    obtain ⟨ψ, hψ⟩ := exists_postComp_eq N PA PB f hf φ χ hχ'
    exact ⟨ψ, hψ⟩
  · rintro ⟨ψ, rfl⟩
    apply Subtype.ext
    apply LinearMap.ext
    intro v
    exact hexact.apply_apply_eq_zero _
end HomExact
p2m_reactivate "P2MW.S_groupCohomology_finrank_continuousH1_eq_invariants_add_dualTwist_add_finrank_mul_of_tame_intermediateField.PDevissage"
end PDevissage
p2m_reactivate "P2MW.S_groupCohomology_finrank_continuousH1_eq_invariants_add_dualTwist_add_finrank_mul_of_tame_intermediateField.PDevissage"

namespace PDevissage
section Alt
variable {k : Type*} [Field k]
  {V₁ V₂ V₃ V₄ V₅ V₆ : Type*} [AddCommGroup V₁] [Module k V₁] [AddCommGroup V₂] [Module k V₂]
  [AddCommGroup V₃] [Module k V₃] [AddCommGroup V₄] [Module k V₄] [AddCommGroup V₅] [Module k V₅]
  [AddCommGroup V₆] [Module k V₆]
  [FiniteDimensional k V₁] [FiniteDimensional k V₂] [FiniteDimensional k V₃] [FiniteDimensional k V₄]
  [FiniteDimensional k V₅] [FiniteDimensional k V₆]

private theorem finrank_alternating_six (u₁ : V₁ →ₗ[k] V₂) (u₂ : V₂ →ₗ[k] V₃) (u₃ : V₃ →ₗ[k] V₄) (u₄ : V₄ →ₗ[k] V₅)
    (u₅ : V₅ →ₗ[k] V₆) (h₁ : Function.Injective u₁) (h₁₂ : Function.Exact u₁ u₂) (h₂₃ : Function.Exact u₂ u₃)
    (h₃₄ : Function.Exact u₃ u₄) (h₄₅ : Function.Exact u₄ u₅) (h₅ : Function.Surjective u₅) :
    finrank k V₁ + finrank k V₃ + finrank k V₅ = finrank k V₂ + finrank k V₄ + finrank k V₆ := by
  have r₁ := LinearMap.finrank_range_add_finrank_ker u₁
  have r₂ := LinearMap.finrank_range_add_finrank_ker u₂
  have r₃ := LinearMap.finrank_range_add_finrank_ker u₃
  have r₄ := LinearMap.finrank_range_add_finrank_ker u₄
  have r₅ := LinearMap.finrank_range_add_finrank_ker u₅
  have e₁ : finrank k (LinearMap.ker u₁) = 0 := by rw [LinearMap.ker_eq_bot.mpr h₁, finrank_bot]
  have e₂ : finrank k (LinearMap.ker u₂) = finrank k (LinearMap.range u₁) := by rw [h₁₂.linearMap_ker_eq]
  have e₃ : finrank k (LinearMap.ker u₃) = finrank k (LinearMap.range u₂) := by rw [h₂₃.linearMap_ker_eq]
  have e₄ : finrank k (LinearMap.ker u₄) = finrank k (LinearMap.range u₃) := by rw [h₃₄.linearMap_ker_eq]
  have e₅ : finrank k (LinearMap.ker u₅) = finrank k (LinearMap.range u₄) := by rw [h₄₅.linearMap_ker_eq]
  have e₆ : finrank k (LinearMap.range u₅) = finrank k V₆ := by rw [LinearMap.range_eq_top.mpr h₅, finrank_top]
  omega

end Alt
p2m_reactivate "P2MW.S_groupCohomology_finrank_continuousH1_eq_invariants_add_dualTwist_add_finrank_mul_of_tame_intermediateField.PDevissage"
end PDevissage
p2m_reactivate "P2MW.S_groupCohomology_finrank_continuousH1_eq_invariants_add_dualTwist_add_finrank_mul_of_tame_intermediateField.PDevissage"

namespace PDevissage

section Equivariance
variable {Δ : Type*} [Group Δ] {A : Type*} [AddCommGroup A] {p : ℕ} [Fact p.Prime]
variable (act : Δ →* AddAut A) (B : AddSubgroup A) (hB : ∀ (d : Δ) (a : A), a ∈ B → act d a ∈ B)

local notation "C" => A ⧸ B

private theorem Ti_equivariant (d : Δ) :
    Ti (p := p) B ∘ₗ torRep (subAct act B hB) d = torRep act d ∘ₗ Ti (p := p) B := by
  ext x; rfl

private theorem Tq_equivariant (d : Δ) :
    Tq (p := p) B ∘ₗ torRep act d = torRep (quotAct act B hB) d ∘ₗ Tq (p := p) B := by
  ext x; rfl

private theorem Qi_equivariant (d : Δ) :
    Qi (p := p) B ∘ₗ quotRep (subAct act B hB) d = quotRep act d ∘ₗ Qi (p := p) B := by
  apply LinearMap.ext; intro x
  induction x using QuotientAddGroup.induction_on with
  | H b => rfl

private theorem Qq_equivariant (d : Δ) :
    Qq (p := p) B ∘ₗ quotRep act d = quotRep (quotAct act B hB) d ∘ₗ Qq (p := p) B := by
  apply LinearMap.ext; intro x
  induction x using QuotientAddGroup.induction_on with
  | H a => rfl

private theorem delta_equivariant (d : Δ) :
    delta (p := p) B ∘ₗ torRep (quotAct act B hB) d = quotRep (subAct act B hB) d ∘ₗ delta (p := p) B := by
  apply LinearMap.ext; intro c
  obtain ⟨a, ha⟩ : ∃ a : A, (QuotientAddGroup.mk a : C) = c := ⟨_, QuotientAddGroup.out_eq' _⟩
  rw [LinearMap.comp_apply, LinearMap.comp_apply, delta_apply B c a ha,
    delta_apply B (torRep (quotAct act B hB) d c) (act d a) (by rw [← quotAct_mk act B hB, ha]; rfl)]
  show _ = QuotientAddGroup.mk _
  congr 1
  apply Subtype.ext
  show p • act d a = act d (p • a)
  rw [map_nsmul]

end Equivariance
p2m_reactivate "P2MW.S_groupCohomology_finrank_continuousH1_eq_invariants_add_dualTwist_add_finrank_mul_of_tame_intermediateField.PDevissage"

section Engine
variable {Δ : Type*} [Group Δ] [Fintype Δ] {A : Type*} [AddCommGroup A] {p : ℕ} [Fact p.Prime]
variable (act : Δ →* AddAut A) (B : AddSubgroup A) (hB : ∀ (d : Δ) (a : A), a ∈ B → act d a ∈ B)
variable {VN : Type*} [AddCommGroup VN] [Module (ZMod p) VN] [FiniteDimensional (ZMod p) VN]
  (N : Representation (ZMod p) Δ VN)

local notation "C" => A ⧸ B

private theorem engine [Invertible (Fintype.card Δ : ZMod p)]
    [FiniteDimensional (ZMod p) (tor B p)] [FiniteDimensional (ZMod p) (tor A p)]
    [FiniteDimensional (ZMod p) (tor C p)] [FiniteDimensional (ZMod p) (B ⧸ pmul B p)]
    [FiniteDimensional (ZMod p) (A ⧸ pmul A p)] [FiniteDimensional (ZMod p) (C ⧸ pmul C p)] :
    finrank (ZMod p) (N.linHom (quotRep (p := p) act)).invariants
      + finrank (ZMod p) (N.linHom (torRep (p := p) (subAct act B hB))).invariants
      + finrank (ZMod p) (N.linHom (torRep (p := p) (quotAct act B hB))).invariants
    = finrank (ZMod p) (N.linHom (torRep (p := p) act)).invariants
      + finrank (ZMod p) (N.linHom (quotRep (p := p) (subAct act B hB))).invariants
      + finrank (ZMod p) (N.linHom (quotRep (p := p) (quotAct act B hB))).invariants := by
  have h := finrank_alternating_six
    (postComp N (torRep (subAct act B hB)) (torRep act) (Ti B) (Ti_equivariant act B hB))
    (postComp N (torRep act) (torRep (quotAct act B hB)) (Tq B) (Tq_equivariant act B hB))
    (postComp N (torRep (quotAct act B hB)) (quotRep (subAct act B hB)) (delta B) (delta_equivariant act B hB))
    (postComp N (quotRep (subAct act B hB)) (quotRep act) (Qi B) (Qi_equivariant act B hB))
    (postComp N (quotRep act) (quotRep (quotAct act B hB)) (Qq B) (Qq_equivariant act B hB))
    (postComp_injective N _ _ _ _ (Ti_injective B))
    (exact_postComp N _ _ _ _ _ _ _ (exact_Ti_Tq B))
    (exact_postComp N _ _ _ _ _ _ _ (exact_Tq_delta B))
    (exact_postComp N _ _ _ _ _ _ _ (exact_delta_Qi B))
    (exact_postComp N _ _ _ _ _ _ _ (exact_Qi_Qq B))
    (postComp_surjective N _ _ _ _ (Qq_surjective B))
  omega

end Engine
p2m_reactivate "P2MW.S_groupCohomology_finrank_continuousH1_eq_invariants_add_dualTwist_add_finrank_mul_of_tame_intermediateField.PDevissage"
end PDevissage
p2m_reactivate "P2MW.S_groupCohomology_finrank_continuousH1_eq_invariants_add_dualTwist_add_finrank_mul_of_tame_intermediateField.PDevissage"

namespace PDevissage

section Aux
variable {k : Type*} [Field k] {Δ : Type*} [Group Δ]
variable {VN : Type*} [AddCommGroup VN] [Module k VN] (N : Representation k Δ VN)

private theorem finrank_hom_eq_of_equiv {VA VB : Type*} [AddCommGroup VA] [Module k VA] [AddCommGroup VB] [Module k VB]
    (PA : Representation k Δ VA) (PB : Representation k Δ VB) (e : VA ≃ₗ[k] VB)
    (he : ∀ (d : Δ) (a : VA), e (PA d a) = PB d (e a)) :
    finrank k (N.linHom PA).invariants = finrank k (N.linHom PB).invariants := by
  have hmemA := mem_invariants_linHom_iff N PA
  have hmemB := mem_invariants_linHom_iff N PB
  let E : (N.linHom PA).invariants ≃ₗ[k] (N.linHom PB).invariants :=
    { toFun := fun φ => ⟨e.toLinearMap ∘ₗ (φ : VN →ₗ[k] VA), (hmemB _).mpr fun d v => by
        simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
        rw [(hmemA _).mp φ.2 d v, he]⟩
      map_add' := fun _ _ => Subtype.ext (by simp [LinearMap.comp_add])
      map_smul' := fun _ _ => Subtype.ext (by simp [LinearMap.comp_smul])
      invFun := fun ψ => ⟨e.symm.toLinearMap ∘ₗ (ψ : VN →ₗ[k] VB), (hmemA _).mpr fun d v => by
        simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
        apply e.injective
        rw [LinearEquiv.apply_symm_apply, he, LinearEquiv.apply_symm_apply]
        exact (hmemB _).mp ψ.2 d v⟩
      left_inv := fun φ => Subtype.ext (LinearMap.ext fun v => by simp)
      right_inv := fun ψ => Subtype.ext (LinearMap.ext fun v => by simp) }
  exact LinearEquiv.finrank_eq E

private theorem finrank_hom_eq_zero_of_subsingleton {VA : Type*} [AddCommGroup VA] [Module k VA] [Subsingleton VA]
    (PA : Representation k Δ VA) : finrank k (N.linHom PA).invariants = 0 := by
  haveI : Subsingleton (VN →ₗ[k] VA) := inferInstance
  apply finrank_zero_of_subsingleton

end Aux
p2m_reactivate "P2MW.S_groupCohomology_finrank_continuousH1_eq_invariants_add_dualTwist_add_finrank_mul_of_tame_intermediateField.PDevissage"

section Finite
variable {Δ : Type*} [Group Δ] [Fintype Δ] {p : ℕ} [Fact p.Prime]
variable {VN : Type*} [AddCommGroup VN] [Module (ZMod p) VN] [FiniteDimensional (ZMod p) VN]
  (N : Representation (ZMod p) Δ VN)

private theorem pmul_stable {A : Type*} [AddCommGroup A] (act : Δ →* AddAut A) (d : Δ) (a : A) (ha : a ∈ pmul A p) :
    act d a ∈ pmul A p := by
  obtain ⟨a', rfl⟩ := ha
  exact ⟨act d a', (map_nsmul _ _ _).symm⟩

private theorem finrank_hom_tor_eq_quot_of_forall_nsmul_eq_zero {A : Type*} [AddCommGroup A] [Finite A]
    (act : Δ →* AddAut A) (hA : ∀ a : A, p • a = 0) :
    finrank (ZMod p) (N.linHom (torRep (p := p) act)).invariants
      = finrank (ZMod p) (N.linHom (quotRep (p := p) act)).invariants := by

  have htor : ∀ a : A, a ∈ tor A p := fun a => mem_tor.mpr (hA a)
  have hpmul : pmul A p = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨a, rfl⟩
    exact hA a

  let f₀ : tor A p →+ A ⧸ pmul A p := (QuotientAddGroup.mk' (pmul A p)).comp (tor A p).subtype
  have hf₀_inj : Function.Injective f₀ := by
    intro x y h
    apply Subtype.ext
    have : ((x : A) : A ⧸ pmul A p) = (y : A) := h
    rwa [QuotientAddGroup.eq, hpmul, AddSubgroup.mem_bot, neg_add_eq_zero] at this
  have hf₀_surj : Function.Surjective f₀ := by
    intro z
    induction z using QuotientAddGroup.induction_on with
    | H a => exact ⟨⟨a, htor a⟩, rfl⟩
  let e : tor A p ≃ₗ[ZMod p] (A ⧸ pmul A p) :=
    LinearEquiv.ofBijective (f₀.toZModLinearMap p) ⟨hf₀_inj, hf₀_surj⟩
  exact finrank_hom_eq_of_equiv N _ _ e (fun d a => rfl)

private scoped instance finiteDimensional_tor {A : Type*} [AddCommGroup A] [Finite A] :
    FiniteDimensional (ZMod p) (tor A p) :=
  Module.Finite.of_finite
private scoped instance finiteDimensional_quot {A : Type*} [AddCommGroup A] [Finite A] :
    FiniteDimensional (ZMod p) (A ⧸ pmul A p) :=
  Module.Finite.of_finite

private theorem finrank_hom_tor_eq_quot_of_finite [Invertible (Fintype.card Δ : ZMod p)] :
    ∀ (n : ℕ) (A : Type*) [AddCommGroup A] [Finite A] (act : Δ →* AddAut A), Nat.card A = n →
      finrank (ZMod p) (N.linHom (torRep (p := p) act)).invariants
        = finrank (ZMod p) (N.linHom (quotRep (p := p) act)).invariants := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro A _ _ act hn
    by_cases htop : pmul A p = ⊤
    ·
      have hsurj : Function.Surjective (fun a : A => p • a) := fun a => by
        have : a ∈ pmul A p := htop ▸ AddSubgroup.mem_top a
        exact this
      have hinj : Function.Injective (fun a : A => p • a) := Finite.injective_iff_surjective.mpr hsurj
      haveI : Subsingleton (tor A p) := ⟨fun x y => Subtype.ext (hinj (by
        simp only [mem_tor.mp x.2, mem_tor.mp y.2]))⟩
      haveI : Subsingleton (A ⧸ pmul A p) := by
        rw [htop]; exact QuotientAddGroup.subsingleton_quotient_top
      rw [finrank_hom_eq_zero_of_subsingleton, finrank_hom_eq_zero_of_subsingleton]
    ·
      set B := pmul A p with hBdef
      have hB : ∀ (d : Δ) (a : A), a ∈ B → act d a ∈ B := pmul_stable act
      haveI : Finite B := inferInstance
      haveI : Finite (A ⧸ B) := inferInstance
      have hcard : Nat.card B < n := by
        rw [← hn]
        have h1 : Nat.card B * B.index = Nat.card A := AddSubgroup.card_mul_index B
        have h2 : B.index ≠ 1 := fun h => htop (AddSubgroup.index_eq_one.mp h)
        have h3 : B.index ≠ 0 := AddSubgroup.index_ne_zero_of_finite
        have h4 : 0 < Nat.card A := Nat.card_pos
        have h5 : 2 ≤ B.index := by omega
        have h6 : Nat.card B * 2 ≤ Nat.card A := h1 ▸ Nat.mul_le_mul_left _ h5
        omega

      have hE := engine act B hB N
      have hIH := ih (Nat.card B) hcard B (subAct act B hB) rfl
      have hC : finrank (ZMod p) (N.linHom (torRep (p := p) (quotAct act B hB))).invariants
          = finrank (ZMod p) (N.linHom (quotRep (p := p) (quotAct act B hB))).invariants :=
        finrank_hom_tor_eq_quot_of_forall_nsmul_eq_zero N (quotAct act B hB) (fun c => by
          induction c using QuotientAddGroup.induction_on with
          | H a => rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]; exact ⟨a, rfl⟩)
      omega

end Finite
p2m_reactivate "P2MW.S_groupCohomology_finrank_continuousH1_eq_invariants_add_dualTwist_add_finrank_mul_of_tame_intermediateField.PDevissage"
end PDevissage
p2m_reactivate "P2MW.S_groupCohomology_finrank_continuousH1_eq_invariants_add_dualTwist_add_finrank_mul_of_tame_intermediateField.PDevissage"

namespace PDevissage

section MainCanonical
variable {Δ : Type*} [Group Δ] [Fintype Δ] {p : ℕ} [Fact p.Prime]
variable {VN : Type*} [AddCommGroup VN] [Module (ZMod p) VN] [FiniteDimensional (ZMod p) VN]
  (N : Representation (ZMod p) Δ VN)

private theorem finrank_hom_canonical_eq [Invertible (Fintype.card Δ : ZMod p)]
    {A : Type*} [AddCommGroup A] (act : Δ →* AddAut A)
    (B : AddSubgroup A) [B.FiniteIndex] (hB : ∀ (d : Δ) (a : A), a ∈ B → act d a ∈ B)
    [FiniteDimensional (ZMod p) (tor B p)] [FiniteDimensional (ZMod p) (tor A p)]
    [FiniteDimensional (ZMod p) (B ⧸ pmul B p)] [FiniteDimensional (ZMod p) (A ⧸ pmul A p)] :
    finrank (ZMod p) (N.linHom (quotRep (p := p) act)).invariants
      + finrank (ZMod p) (N.linHom (torRep (p := p) (subAct act B hB))).invariants
    = finrank (ZMod p) (N.linHom (quotRep (p := p) (subAct act B hB))).invariants
      + finrank (ZMod p) (N.linHom (torRep (p := p) act)).invariants := by
  haveI : Finite (A ⧸ B) := AddSubgroup.finite_quotient_of_finiteIndex
  have hE := engine act B hB N
  have hC := finrank_hom_tor_eq_quot_of_finite N (Nat.card (A ⧸ B)) (A ⧸ B) (quotAct act B hB) rfl
  omega

end MainCanonical
p2m_reactivate "P2MW.S_groupCohomology_finrank_continuousH1_eq_invariants_add_dualTwist_add_finrank_mul_of_tame_intermediateField.PDevissage"

section Transfer
variable {Δ : Type*} [Group Δ] {p : ℕ} [Fact p.Prime]
variable {VN : Type*} [AddCommGroup VN] [Module (ZMod p) VN] (N : Representation (ZMod p) Δ VN)
variable {A : Type*} [AddCommGroup A] (act : Δ →* AddAut A)

private theorem quotPres_bijective {VA : Type*} [AddCommGroup VA] [Module (ZMod p) VA]
    (πA : A →+ VA) (hπA : Function.Surjective πA) (hkerA : ∀ a : A, πA a = 0 ↔ ∃ a' : A, p • a' = a) :
    Function.Bijective (QuotientAddGroup.lift (pmul A p) πA
      (by rintro _ ⟨a, rfl⟩; exact (hkerA _).mpr ⟨a, rfl⟩) : A ⧸ pmul A p →+ VA) := by
  constructor
  · intro x y h
    induction x using QuotientAddGroup.induction_on with
    | H a =>
      induction y using QuotientAddGroup.induction_on with
      | H b =>
        change πA a = πA b at h
        rw [QuotientAddGroup.eq]
        have : πA (-a + b) = 0 := by rw [map_add, map_neg, h, neg_add_cancel]
        obtain ⟨a', ha'⟩ := (hkerA _).mp this
        exact ⟨a', ha'⟩
  · intro v
    obtain ⟨a, rfl⟩ := hπA v
    exact ⟨QuotientAddGroup.mk a, rfl⟩

private noncomputable def quotPresEquiv {VA : Type*} [AddCommGroup VA] [Module (ZMod p) VA]
    (πA : A →+ VA) (hπA : Function.Surjective πA) (hkerA : ∀ a : A, πA a = 0 ↔ ∃ a' : A, p • a' = a) :
    (A ⧸ pmul A p) ≃ₗ[ZMod p] VA :=
  LinearEquiv.ofBijective ((QuotientAddGroup.lift (pmul A p) πA
      (by rintro _ ⟨a, rfl⟩; exact (hkerA _).mpr ⟨a, rfl⟩)).toZModLinearMap p) (quotPres_bijective πA hπA hkerA)

private theorem quotPresEquiv_mk {VA : Type*} [AddCommGroup VA] [Module (ZMod p) VA]
    (πA : A →+ VA) (hπA : Function.Surjective πA) (hkerA : ∀ a : A, πA a = 0 ↔ ∃ a' : A, p • a' = a) (a : A) :
    quotPresEquiv πA hπA hkerA (QuotientAddGroup.mk a) = πA a := rfl

private theorem finrank_hom_quotPres_eq
    {VA : Type*} [AddCommGroup VA] [Module (ZMod p) VA] (PA : Representation (ZMod p) Δ VA)
    (πA : A →+ VA) (hπA : Function.Surjective πA) (hkerA : ∀ a : A, πA a = 0 ↔ ∃ a' : A, p • a' = a)
    (hπAΔ : ∀ (d : Δ) (a : A), πA (act d a) = PA d (πA a)) :
    finrank (ZMod p) (N.linHom PA).invariants = finrank (ZMod p) (N.linHom (quotRep (p := p) act)).invariants := by
  symm
  refine finrank_hom_eq_of_equiv N _ _ (quotPresEquiv πA hπA hkerA) (fun d x => ?_)
  induction x using QuotientAddGroup.induction_on with
  | H a => exact hπAΔ d a

private theorem finiteDimensional_quot_of_pres
    {VA : Type*} [AddCommGroup VA] [Module (ZMod p) VA] [FiniteDimensional (ZMod p) VA]
    (πA : A →+ VA) (hπA : Function.Surjective πA) (hkerA : ∀ a : A, πA a = 0 ↔ ∃ a' : A, p • a' = a) :
    FiniteDimensional (ZMod p) (A ⧸ pmul A p) :=
  LinearEquiv.finiteDimensional (quotPresEquiv πA hπA hkerA).symm

private theorem torPres_bijective {WA : Type*} [AddCommGroup WA] [Module (ZMod p) WA]
    (ιA : WA →+ A) (hιA : Function.Injective ιA) (hranA : ∀ a : A, a ∈ Set.range ιA ↔ p • a = 0) :
    Function.Bijective (ιA.codRestrict (tor A p) (fun w => mem_tor.mpr ((hranA _).mp ⟨w, rfl⟩))) := by
  constructor
  · exact fun x y h => hιA (congrArg Subtype.val h)
  · rintro ⟨a, ha⟩
    obtain ⟨w, rfl⟩ := (hranA a).mpr (mem_tor.mp ha)
    exact ⟨w, rfl⟩

private noncomputable def torPresEquiv {WA : Type*} [AddCommGroup WA] [Module (ZMod p) WA]
    (ιA : WA →+ A) (hιA : Function.Injective ιA) (hranA : ∀ a : A, a ∈ Set.range ιA ↔ p • a = 0) :
    WA ≃ₗ[ZMod p] tor A p :=
  LinearEquiv.ofBijective ((ιA.codRestrict (tor A p)
    (fun w => mem_tor.mpr ((hranA _).mp ⟨w, rfl⟩))).toZModLinearMap p) (torPres_bijective ιA hιA hranA)

private theorem finrank_hom_torPres_eq
    {WA : Type*} [AddCommGroup WA] [Module (ZMod p) WA] (TA : Representation (ZMod p) Δ WA)
    (ιA : WA →+ A) (hιA : Function.Injective ιA) (hranA : ∀ a : A, a ∈ Set.range ιA ↔ p • a = 0)
    (hιAΔ : ∀ (d : Δ) (w : WA), ιA (TA d w) = act d (ιA w)) :
    finrank (ZMod p) (N.linHom TA).invariants = finrank (ZMod p) (N.linHom (torRep (p := p) act)).invariants :=
  finrank_hom_eq_of_equiv N _ _ (torPresEquiv ιA hιA hranA) (fun d w => Subtype.ext (hιAΔ d w))

private theorem finiteDimensional_tor_of_pres
    {WA : Type*} [AddCommGroup WA] [Module (ZMod p) WA] [FiniteDimensional (ZMod p) WA]
    (ιA : WA →+ A) (hιA : Function.Injective ιA) (hranA : ∀ a : A, a ∈ Set.range ιA ↔ p • a = 0) :
    FiniteDimensional (ZMod p) (tor A p) :=
  LinearEquiv.finiteDimensional (torPresEquiv ιA hιA hranA)

end Transfer
p2m_reactivate "P2MW.S_groupCohomology_finrank_continuousH1_eq_invariants_add_dualTwist_add_finrank_mul_of_tame_intermediateField.PDevissage"
end PDevissage
p2m_reactivate "P2MW.S_groupCohomology_finrank_continuousH1_eq_invariants_add_dualTwist_add_finrank_mul_of_tame_intermediateField.PDevissage"

set_option maxHeartbeats 16000000 in
set_option synthInstance.maxHeartbeats 3200000 in
open PDevissage in

theorem solution
    {p : ℕ} [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    (Kw : IntermediateField K (PadicAlgCl p)) [FiniteDimensional K Kw] [IsGalois K Kw]
    (htame : ¬ p ∣ Module.finrank K Kw)
    (M : Rep.{0} (ZMod p) (PadicAlgCl p ≃ₐ[K] PadicAlgCl p)) [FiniteDimensional (ZMod p) M]
    (htriv : ∀ s ∈ Kw.fixingSubgroup, M.ρ s = 1)
    (hχ : ∀ s ∈ Kw.fixingSubgroup,
      cycloChar p (localGaloisToGlobal p ((IntermediateField.fixingSubgroupEquiv K).symm s)) = 1) :
    Module.finrank (ZMod p) (continuousH1 ((localGaloisToGlobal p).comp ((K.fixingSubgroup.subtype).comp (IntermediateField.fixingSubgroupEquiv K).symm.toMonoidHom)) M)
      = Module.finrank (ZMod p) M.ρ.invariants
        + Module.finrank (ZMod p) (M.dualTwist ((cycloChar p).comp ((localGaloisToGlobal p).comp ((K.fixingSubgroup.subtype).comp (IntermediateField.fixingSubgroupEquiv K).symm.toMonoidHom)))).ρ.invariants
        + Module.finrank ℚ_[p] K * Module.finrank (ZMod p) M := by
  classical
  haveI : IsGalois ℚ_[p] (PadicAlgCl p) := IsAlgClosure.isGalois ℚ_[p] (PadicAlgCl p)
  haveI : IsGalois K (PadicAlgCl p) := IsGalois.tower_top_intermediateField K

  let Γ := PadicAlgCl p ≃ₐ[K] PadicAlgCl p
  let eK := IntermediateField.fixingSubgroupEquiv K
  let rΓ : Γ →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :=
    (localGaloisToGlobal p).comp ((K.fixingSubgroup.subtype).comp eK.symm.toMonoidHom)
  let χΓ : Γ →* (ZMod p)ˣ := (cycloChar p).comp rΓ
  have heK : ∀ (g : Γ) (y : PadicAlgCl p),
      ((eK.symm g : K.fixingSubgroup) : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) y = g y := by
    intro g y
    have : ∀ (x : K.fixingSubgroup) (y : PadicAlgCl p), (eK x) y = (x : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) y :=
      fun _ _ => rfl
    have h := this (eK.symm g) y
    rw [MulEquiv.apply_symm_apply] at h
    exact h.symm
  have hrΓ : ∀ g : Γ, rΓ g = localGaloisToGlobal p ((eK.symm g : K.fixingSubgroup) : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) :=
    fun _ => rfl
  let MΓ : Rep (ZMod p) Γ := M
  suffices hgoal : Module.finrank (ZMod p) (continuousH1 rΓ MΓ)
      = Module.finrank (ZMod p) MΓ.ρ.invariants + Module.finrank (ZMod p) (MΓ.dualTwist χΓ).ρ.invariants
        + Module.finrank ℚ_[p] K * Module.finrank (ZMod p) MΓ by
    exact hgoal

  let S : Subgroup Γ := Kw.fixingSubgroup
  haveI hSnormal : S.Normal := (InfiniteGalois.normal_iff_isGalois Kw).mpr inferInstance
  have hidx : S.index = Module.finrank K Kw := (IntermediateField.finrank_eq_fixingSubgroup_index (L := Kw)).symm
  haveI : S.FiniteIndex := ⟨by rw [hidx]; exact Module.finrank_pos.ne'⟩
  have hunitS : IsUnit ((S.index : ZMod p)) := by
    rw [isUnit_iff_ne_zero, Ne, ZMod.natCast_eq_zero_iff, hidx]
    exact htame

  obtain ⟨ζ, hζp, hζ0⟩ := exists_isPrimitiveRoot_smul_eq_pow_cycloChar_localGaloisToGlobal p p
  have hζ : ∀ g : Γ, g • ζ = ζ ^ (χΓ g : ZMod p).val := by
    intro g
    have h := hζ0 ((eK.symm g : K.fixingSubgroup) : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
    apply Units.ext
    have h' := congrArg (fun u : (PadicAlgCl p)ˣ => (u : PadicAlgCl p)) h
    simp only [Units.val_pow_eq_pow_val] at h' ⊢
    show g (ζ : PadicAlgCl p) = _
    rw [← heK g]
    exact h'
  have hSfix : ∀ s ∈ S, s (ζ : PadicAlgCl p) = ζ := by
    intro s hs
    have h2 : (χΓ s : ZMod p) = 1 := by
      show ((cycloChar p (localGaloisToGlobal p ((eK.symm s : K.fixingSubgroup) : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)) : (ZMod p)ˣ) : ZMod p) = 1
      rw [hχ s hs, Units.val_one]
    have h := congrArg (fun u : (PadicAlgCl p)ˣ => (u : PadicAlgCl p)) (hζ s)
    simp only [h2, ZMod.val_one, pow_one] at h
    exact h
  have hζK : (ζ : PadicAlgCl p) ∈ Kw := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup Kw, IntermediateField.mem_fixedField_iff]
    intro s hs
    exact hSfix s hs
  have hKG : ∀ (g : Γ) (x : PadicAlgCl p), x ∈ Kw → g x ∈ Kw := by
    intro g x hx
    rw [← InfiniteGalois.fixedField_fixingSubgroup Kw, IntermediateField.mem_fixedField_iff]
    intro s hs
    have hs' : g⁻¹ * s * g⁻¹⁻¹ ∈ S := hSnormal.conj_mem s hs g⁻¹
    rw [inv_inv] at hs'
    have := (IntermediateField.mem_fixingSubgroup_iff _ _).mp hs' x hx
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, AlgEquiv.aut_inv] at this
    have := congrArg g this
    rwa [AlgEquiv.apply_symm_apply] at this
  have hroots : ∀ a : PadicAlgCl p, a ∈ Kw → a ≠ 0 → ∃ α : PadicAlgCl p, α ^ p = a :=
    fun a _ _ => IsAlgClosed.exists_pow_nat_eq a (Fact.out : p.Prime).pos

  have htriv' : ∀ s ∈ S, ∀ v : MΓ, MΓ.ρ s v = v := fun s hs v => by rw [htriv s hs]; rfl
  let W : Submodule (ZMod p) (cocycles₁ (Rep.res S.subtype MΓ)) :=
    { carrier := {c | IsLevelConstant₁ (rΓ.comp S.subtype) c.val ∧
        ∀ (g : Γ) (s t : S), (g⁻¹ * s * g : Γ) = t → MΓ.ρ g (c t) = c s}
      zero_mem' := by
        refine ⟨⟨⊥, inferInstance, fun _ _ _ => rfl⟩, fun g s t _ => ?_⟩
        have h0 : ((0 : cocycles₁ (Rep.res S.subtype MΓ)) : S → MΓ) = 0 := rfl
        show MΓ.ρ g (((0 : cocycles₁ (Rep.res S.subtype MΓ)) : S → MΓ) t) = ((0 : cocycles₁ (Rep.res S.subtype MΓ)) : S → MΓ) s
        rw [h0, Pi.zero_apply, Pi.zero_apply, map_zero]
      add_mem' := by
        rintro a b ⟨⟨F₁, hF₁, ha⟩, ha'⟩ ⟨⟨F₂, hF₂, hb⟩, hb'⟩
        haveI := hF₁; haveI := hF₂
        refine ⟨⟨F₁ ⊔ F₂, inferInstance, fun g s hs => ?_⟩, fun g s t hst => ?_⟩
        · show a.val (g * s) + b.val (g * s) = a.val g + b.val g
          rw [ha g s (IntermediateField.fixingSubgroup_antitone le_sup_left hs),
            hb g s (IntermediateField.fixingSubgroup_antitone le_sup_right hs)]
        · show MΓ.ρ g (a t + b t) = a s + b s
          rw [map_add, ha' g s t hst, hb' g s t hst]
      smul_mem' := by
        rintro k a ⟨⟨F₁, hF₁, ha⟩, ha'⟩
        refine ⟨⟨F₁, hF₁, fun g s hs => ?_⟩, fun g s t hst => ?_⟩
        · show k • a.val (g * s) = k • a.val g
          rw [ha g s hs]
        · show MΓ.ρ g (k • a t) = k • a s
          rw [map_smul, ha' g s t hst] }
  have hW : ∀ c, c ∈ W ↔ (IsLevelConstant₁ (rΓ.comp S.subtype) c.val ∧
      ∀ (g : Γ) (s t : S), (g⁻¹ * s * g : Γ) = t → MΓ.ρ g (c t) = c s) :=
    fun _ => Iff.rfl

  have hSopen : ∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧
      ∀ s : Γ, rΓ s ∈ F₀.fixingSubgroup → s ∈ S := by
    haveI : FiniteDimensional ℚ_[p] (Kw.restrictScalars ℚ_[p]) := by
      show FiniteDimensional ℚ_[p] Kw
      exact FiniteDimensional.trans ℚ_[p] K Kw
    obtain ⟨F₀, hF₀fd, hle⟩ := IntermediateField.exists_le_adjoin_padicEmbedding_image p (Kw.restrictScalars ℚ_[p])
    refine ⟨F₀, hF₀fd, fun s hs => ?_⟩
    have hs' := (localGaloisToGlobal_mem_fixingSubgroup_iff p F₀
      ((eK.symm s : K.fixingSubgroup) : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)).mp hs
    rw [IntermediateField.mem_fixingSubgroup_iff] at hs' ⊢
    intro y hy
    rw [← heK]
    exact hs' y (hle hy)
  have h1 := groupCohomology.finrank_continuousClasses_eq_finrank_of_isUnit_index_of_forall_apply_eq
    rΓ MΓ S hunitS htriv' hSopen (continuousH1 rΓ MΓ) (fun x => mem_continuousH1_iff rΓ MΓ x) W hW

  let resK : Γ →* (Kw ≃ₐ[K] Kw) := AlgEquiv.restrictNormalHom Kw
  have hresK : ∀ (g : Γ) (x : Kw), ((resK g x : Kw) : PadicAlgCl p) = g x :=
    fun g x => AlgEquiv.restrictNormal_commutes g Kw x
  have hresK_surj : Function.Surjective resK := AlgEquiv.restrictNormalHom_surjective _
  have hinvK : ∀ (σ : Kw ≃ₐ[K] Kw) (x : Kw), σ⁻¹ (σ x) = x := fun σ x => by
    rw [AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]
  have hinvK' : ∀ (σ : Kw ≃ₐ[K] Kw) (x : Kw), σ (σ⁻¹ x) = x := fun σ x => by
    rw [AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply]
  let ψK : (Kw ≃ₐ[K] Kw) → ((↥Kw)ˣ ≃* (↥Kw)ˣ) := fun σ =>
    { toFun := fun u => Units.map (σ : Kw →* Kw) u
      invFun := fun u => Units.map ((σ⁻¹ : Kw ≃ₐ[K] Kw) : Kw →* Kw) u
      left_inv := fun u => Units.ext (hinvK σ _)
      right_inv := fun u => Units.ext (hinvK' σ _)
      map_mul' := fun u v => map_mul _ _ _ }
  let actXK : (Kw ≃ₐ[K] Kw) →* AddAut (Additive (↥Kw)ˣ) :=
    { toFun := fun σ => MulEquiv.toAdditive (ψK σ)
      map_one' := by
        apply AddEquiv.ext
        intro a
        obtain ⟨u, rfl⟩ : ∃ u, Additive.ofMul u = a := ⟨Additive.toMul a, rfl⟩
        show Additive.ofMul (ψK 1 u) = Additive.ofMul u
        congr 1
      map_mul' := fun σ τ => by
        apply AddEquiv.ext
        intro a
        obtain ⟨u, rfl⟩ : ∃ u, Additive.ofMul u = a := ⟨Additive.toMul a, rfl⟩
        show Additive.ofMul (ψK (σ * τ) u) = Additive.ofMul (ψK σ (ψK τ u))
        congr 1 }
  have actXK_apply : ∀ (σ : Kw ≃ₐ[K] Kw) (u : (↥Kw)ˣ),
      actXK σ (Additive.ofMul u) = Additive.ofMul (Units.map (σ : Kw →* Kw) u) := fun _ _ => rfl
  let PFK : Representation (ZMod p) (Kw ≃ₐ[K] Kw) (Additive (↥Kw)ˣ ⧸ pmul (Additive (↥Kw)ˣ) p) :=
    quotRep actXK
  let X : Representation (ZMod p) (Γ) (Additive (↥Kw)ˣ ⧸ pmul (Additive (↥Kw)ˣ) p) :=
    PFK.comp resK
  have hX : ∀ g, X g = PFK (resK g) := fun _ => rfl
  let π : (↥Kw)ˣ → Additive (↥Kw)ˣ ⧸ pmul (Additive (↥Kw)ˣ) p := fun a => QuotientAddGroup.mk (Additive.ofMul a)
  have hπ : ∀ a, π a = QuotientAddGroup.mk (Additive.ofMul a) := fun _ => rfl
  have hπmul : ∀ a b, π (a * b) = π a + π b := fun a b => by
    rw [hπ, hπ, hπ, ofMul_mul, QuotientAddGroup.mk_add]
  have hπsurj : Function.Surjective π := fun z => by
    induction z using QuotientAddGroup.induction_on with
    | H a => exact ⟨Additive.toMul a, rfl⟩
  have hcanK : ∀ a : Additive (↥Kw)ˣ, (QuotientAddGroup.mk a : Additive (↥Kw)ˣ ⧸ pmul (Additive (↥Kw)ˣ) p) = 0
      ↔ a ∈ pmul (Additive (↥Kw)ˣ) p := fun a => QuotientAddGroup.eq_zero_iff a
  have hπker : ∀ a : (↥Kw)ˣ, π a = 0 ↔ ∃ b : (↥Kw)ˣ, b ^ p = a := by
    intro a
    rw [hπ, hcanK, mem_pmul]
    constructor
    · rintro ⟨a', ha'⟩
      obtain ⟨w, rfl⟩ : ∃ w, Additive.ofMul w = a' := ⟨Additive.toMul a', rfl⟩
      exact ⟨w, Additive.ofMul.injective (by rw [ofMul_pow]; exact ha')⟩
    · rintro ⟨w, hw⟩; exact ⟨Additive.ofMul w, by rw [← ofMul_pow, hw]⟩
  have hπG : ∀ (g : Γ) (a b : (↥Kw)ˣ),
      g ((a : Kw) : PadicAlgCl p) = ((b : Kw) : PadicAlgCl p) → X g (π a) = π b := by
    intro g a b h
    show PFK (resK g) (QuotientAddGroup.mk (Additive.ofMul a)) = QuotientAddGroup.mk (Additive.ofMul b)
    show quotRep actXK (resK g) (QuotientAddGroup.mk (Additive.ofMul a)) = _
    rw [quotRep_mk, actXK_apply]
    congr 2
    apply Units.ext
    apply Subtype.ext
    show ((resK g (a : Kw) : Kw) : PadicAlgCl p) = ((b : Kw) : PadicAlgCl p)
    rw [hresK]
    exact h
  have hWnat : ∀ c, c ∈ W ↔
      (∃ E : IntermediateField K (PadicAlgCl p), FiniteDimensional K E ∧
        ∀ (g s : S), (s : Γ) ∈ E.fixingSubgroup → c (g * s) = c g) ∧
      ∀ (g : Γ) (s t : S), (g⁻¹ * s * g : Γ) = t → MΓ.ρ g (c t) = c s := by
    intro c
    rw [hW]
    apply and_congr_left'

    have hD := exists_finiteDimensional_comap_localGaloisToGlobal_iff p
      (fun U => ∀ g s : S, ((eK.symm (s : Γ) : K.fixingSubgroup) : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) ∈ U →
        c (g * s) = c g)
      (fun U V hVU hU g s hs => hU g s (hVU hs))
    refine hD.trans ⟨?_, ?_⟩
    · rintro ⟨E', hE'fd, hE'⟩
      haveI := hE'fd
      let bE := Module.finBasis ℚ_[p] E'
      let T : Set (PadicAlgCl p) := Set.range (fun i => ((bE i : E') : PadicAlgCl p))
      haveI : Finite T := Set.finite_range _ |>.to_subtype
      let E : IntermediateField K (PadicAlgCl p) := IntermediateField.adjoin K T
      haveI : FiniteDimensional K E := IntermediateField.finiteDimensional_adjoin (fun x _ =>
        (Algebra.IsIntegral.isIntegral (R := ℚ_[p]) x).tower_top)
      have hE'E : ∀ y : PadicAlgCl p, y ∈ E' → y ∈ E := by
        intro y hy
        have hspan := bE.mem_span (⟨y, hy⟩ : E')
        have : ((⟨y, hy⟩ : E') : PadicAlgCl p) ∈ (Submodule.span ℚ_[p] (Set.range bE)).map
            ((E'.val : E' →ₐ[ℚ_[p]] PadicAlgCl p).toLinearMap) := Submodule.mem_map_of_mem hspan
        rw [Submodule.map_span] at this
        have hle : Submodule.span ℚ_[p] (((E'.val : E' →ₐ[ℚ_[p]] PadicAlgCl p).toLinearMap) '' Set.range bE)
            ≤ (E.toSubalgebra.toSubmodule).restrictScalars ℚ_[p] := by
          refine Submodule.span_le.mpr ?_
          rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
          exact IntermediateField.subset_adjoin K T ⟨i, rfl⟩
        exact hle this
      refine ⟨E, inferInstance, fun g s hs => hE' g s ?_⟩
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro y hy
      rw [heK]
      exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp hs y (hE'E y hy)
    · rintro ⟨E, hEfd, hE⟩
      haveI := hEfd
      refine ⟨E.restrictScalars ℚ_[p], ?_, fun g s hs => hE g s ?_⟩
      · show FiniteDimensional ℚ_[p] E
        exact FiniteDimensional.trans ℚ_[p] K E
      · rw [IntermediateField.mem_fixingSubgroup_iff]
        intro y hy
        rw [← heK]
        exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp hs y hy
  have h2 := groupCohomology.finrank_continuousEquivariantHom_eq_finrank_invariants_linHom_dualTwist
    Kw hKG χΓ hζp hζ hζK hroots MΓ htriv' W hWnat X π hπmul hπsurj
    hπker hπG

  have hkerS : ∀ g : Γ, resK g = 1 ↔ g ∈ S := by
    intro g
    show resK g = 1 ↔ g ∈ Kw.fixingSubgroup
    rw [IntermediateField.mem_fixingSubgroup_iff]
    constructor
    · intro h x hx
      have := hresK g ⟨x, hx⟩
      rw [h] at this
      simpa using this.symm
    · intro h
      apply AlgEquiv.ext
      intro x
      apply Subtype.ext
      rw [hresK]
      exact h x x.2

  let ρD : Representation (ZMod p) (Γ) (MΓ.dualTwist (χΓ)) :=
    (MΓ.dualTwist (χΓ)).ρ
  have hρD : ∀ g (f : Module.Dual (ZMod p) MΓ), ρD g f
      = ((χΓ) g : ZMod p) • (f ∘ₗ MΓ.ρ g⁻¹) := fun g f => by
    show (MΓ.ρ.dual.twist _) g f = _
    rw [Representation.twist_apply_apply, Representation.dual_apply, Module.Dual.transpose_apply]
  have hρD_S : ∀ s ∈ S, ρD s = LinearMap.id := by
    intro s hs
    apply LinearMap.ext
    intro f
    rw [hρD, LinearMap.id_apply]
    have h2 : χΓ s = 1 := by
      show cycloChar p (localGaloisToGlobal p ((eK.symm s : K.fixingSubgroup) : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)) = 1
      exact hχ s hs
    have h1 : MΓ.ρ s⁻¹ = 1 := htriv s⁻¹ (S.inv_mem hs)
    rw [h2, Units.val_one, one_smul, h1]
    ext v; rfl
  have hρD_eq : ∀ g g' : Γ, resK g = resK g' → ρD g = ρD g' := by
    intro g g' h
    have hmem : g'⁻¹ * g ∈ S := by
      rw [← hkerS, map_mul, map_inv, h, inv_mul_cancel]
    have := hρD_S _ hmem
    calc ρD g = ρD (g' * (g'⁻¹ * g)) := by rw [mul_inv_cancel_left]
      _ = ρD g' * ρD (g'⁻¹ * g) := map_mul _ _ _
      _ = ρD g' := by rw [this]; exact mul_one _

  let sec : (Kw ≃ₐ[K] Kw) → Γ := Function.surjInv hresK_surj
  have hsec : ∀ δ, resK (sec δ) = δ := Function.surjInv_eq hresK_surj
  let ND : Representation (ZMod p) (Kw ≃ₐ[K] Kw) (MΓ.dualTwist (χΓ)) :=
    { toFun := fun δ => ρD (sec δ)
      map_one' := by
        rw [← map_one ρD]
        exact hρD_eq _ _ (by rw [hsec, map_one])
      map_mul' := fun δ δ' => by
        rw [← map_mul ρD]
        exact hρD_eq _ _ (by rw [hsec, map_mul, hsec, hsec]) }
  have hND : ∀ g : Γ, ND (resK g) = ρD g := fun g => hρD_eq _ _ (hsec _)

  have hdesc : ∀ {VY : Type} [AddCommGroup VY] [Module (ZMod p) VY]
      (Y : Representation (ZMod p) (Kw ≃ₐ[K] Kw) VY),
      (ρD.linHom (Y.comp resK)).invariants = (ND.linHom Y).invariants := by
    intro VY _ _ Y
    ext φ
    rw [Representation.mem_invariants, Representation.mem_invariants]
    constructor
    · intro h δ
      obtain ⟨g, rfl⟩ := hresK_surj δ
      have := h g
      rw [Representation.linHom_apply] at this ⊢
      rw [← map_inv, hND]
      exact this
    · intro h g
      have := h (resK g)
      rw [Representation.linHom_apply] at this ⊢
      rw [← map_inv, hND] at this
      exact this
  have h3 : finrank (ZMod p) (ρD.linHom X).invariants = finrank (ZMod p) (ND.linHom PFK).invariants := by
    rw [show X = PFK.comp resK from rfl, hdesc PFK]

  haveI : (pmul (Additive (↥Kw)ˣ) p).Normal := ⟨fun n hn g => by rwa [add_comm g n, add_neg_cancel_right]⟩
  let πF : Additive (↥Kw)ˣ →+ Additive (↥Kw)ˣ ⧸ pmul (Additive (↥Kw)ˣ) p :=
    QuotientAddGroup.mk' (pmul (Additive (↥Kw)ˣ) p)
  have hπF_surj : Function.Surjective πF := QuotientAddGroup.mk'_surjective _
  have hcanKΔ : ∀ (σ : Kw ≃ₐ[K] Kw) (u : (↥Kw)ˣ),
      πF (Additive.ofMul (Units.map (σ : Kw →* Kw) u)) = PFK σ (πF (Additive.ofMul u)) := fun _ _ => rfl
  have hπker' : ∀ u : (↥Kw)ˣ, πF (Additive.ofMul u) = 0 ↔ ∃ b : (↥Kw)ˣ, b ^ p = u := fun u => hπker u
  have hranT : ∀ u : (↥Kw)ˣ, Additive.ofMul u ∈ Set.range ((tor (Additive (↥Kw)ˣ) p).subtype) ↔ u ^ p = 1 := by
    intro u
    constructor
    · rintro ⟨z, hz⟩
      change (z : Additive (↥Kw)ˣ) = Additive.ofMul u at hz
      have := mem_tor.mp z.2
      rw [hz, ← ofMul_pow, ← ofMul_one, Additive.ofMul.injective.eq_iff] at this
      exact this
    · intro h
      exact ⟨⟨Additive.ofMul u, mem_tor.mpr (by rw [← ofMul_pow, h, ofMul_one])⟩, rfl⟩
  have hKw := ExtCitation.LocalLevel.finrank_invariants_linHom_unitsModPow_of_isGalois_intermediateField p K Kw
    htame ND PFK πF hπF_surj hπker' hcanKΔ
    (torRep actXK) ((tor (Additive (↥Kw)ˣ) p).subtype) (fun x y h => Subtype.ext h) hranT (fun σ v => rfl)

  have hF1 : finrank (ZMod p) (MΓ.dualTwist χΓ) = finrank (ZMod p) MΓ := Subspace.dual_finrank_eq

  have hζne : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  let ζKw : Kw := ⟨ζ, hζK⟩
  have hζKw : IsPrimitiveRoot ζKw p :=
    IsPrimitiveRoot.of_map_of_injective (f := algebraMap Kw (PadicAlgCl p))
      (IsPrimitiveRoot.coe_units_iff.mpr hζp) (algebraMap Kw (PadicAlgCl p)).injective
  let ζK : (↥Kw)ˣ := (hζKw.isUnit hζne).unit
  have hζK_coe : (ζK : Kw) = ζKw := IsUnit.unit_spec _
  have hζKu : IsPrimitiveRoot ζK p := IsPrimitiveRoot.coe_units_iff.mp (by rw [hζK_coe]; exact hζKw)
  have hζK1 : ζK ^ p = 1 := hζKu.pow_eq_one
  have hpowmod : ∀ n : ℕ, ζK ^ (n % p) = ζK ^ n := fun n => by
    conv_rhs => rw [← Nat.mod_add_div n p, pow_add, pow_mul, hζK1, one_pow, mul_one]

  have hζval : ∀ g : Γ, g (ζ : PadicAlgCl p) = ((ζ ^ (χΓ g : ZMod p).val : (PadicAlgCl p)ˣ) : PadicAlgCl p) := by
    intro g
    have h := congrArg (fun u : (PadicAlgCl p)ˣ => (u : PadicAlgCl p)) (hζ g)
    first | simpa using h | exact h | (simp at h; exact h)
  have hζK_act : ∀ g : Γ, Units.map (resK g : Kw →* Kw) ζK = ζK ^ (χΓ g : ZMod p).val := by
    intro g
    apply Units.ext
    apply Subtype.ext
    show ((resK g (ζK : Kw) : Kw) : PadicAlgCl p) = (((ζK ^ (χΓ g : ZMod p).val : (↥Kw)ˣ) : Kw) : PadicAlgCl p)
    rw [hresK, hζK_coe]
    show g (ζ : PadicAlgCl p) = _
    rw [hζval, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hζK_coe]
    rfl

  let f₀ : ZMod p → tor (Additive (↥Kw)ˣ) p := fun c =>
    ⟨Additive.ofMul (ζK ^ c.val), mem_tor.mpr (by
      rw [← ofMul_pow, ← ofMul_one, ← pow_mul, mul_comm, pow_mul, hζK1, one_pow])⟩
  have hf₀ : ∀ c, ((f₀ c : tor (Additive (↥Kw)ˣ) p) : Additive (↥Kw)ˣ) = Additive.ofMul (ζK ^ c.val) := fun _ => rfl
  have hf₀_add : ∀ a b, f₀ (a + b) = f₀ a + f₀ b := by
    intro a b
    apply Subtype.ext
    show Additive.ofMul (ζK ^ (a + b).val) = Additive.ofMul (ζK ^ a.val) + Additive.ofMul (ζK ^ b.val)
    rw [← ofMul_mul, ← pow_add, ZMod.val_add, hpowmod]
  let fA : ZMod p →+ tor (Additive (↥Kw)ˣ) p :=
    { toFun := f₀, map_zero' := Subtype.ext (by show Additive.ofMul (ζK ^ (0 : ZMod p).val) = 0; rw [ZMod.val_zero, pow_zero, ofMul_one]), map_add' := hf₀_add }
  have hfA_inj : Function.Injective fA := by
    intro a b h
    have h' : ζK ^ a.val = ζK ^ b.val := Additive.ofMul.injective (congrArg (fun z : tor (Additive (↥Kw)ˣ) p => (z : Additive (↥Kw)ˣ)) h)
    rw [pow_eq_pow_iff_modEq, ← hζKu.eq_orderOf] at h'
    have := (ZMod.natCast_eq_natCast_iff _ _ _).mpr h'
    rwa [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at this
  have hfA_surj : Function.Surjective fA := by
    rintro ⟨a, ha⟩
    obtain ⟨u, rfl⟩ : ∃ u, Additive.ofMul u = a := ⟨Additive.toMul a, rfl⟩
    have hu : u ^ p = 1 := by
      have := mem_tor.mp ha
      rwa [← ofMul_pow, ← ofMul_one, Additive.ofMul.injective.eq_iff] at this
    have hu' : ((u : (↥Kw)ˣ) : Kw) ^ p = 1 := by rw [← Units.val_pow_eq_pow_val, hu, Units.val_one]
    obtain ⟨i, -, hi⟩ := hζKw.eq_pow_of_pow_eq_one hu'
    have hi' : ζK ^ i = u := Units.ext (by rw [Units.val_pow_eq_pow_val, hζK_coe, hi])
    refine ⟨(i : ZMod p), Subtype.ext ?_⟩
    show Additive.ofMul (ζK ^ (i : ZMod p).val) = Additive.ofMul u
    rw [ZMod.val_natCast, hpowmod, hi']
  let eμ : ZMod p ≃ₗ[ZMod p] tor (Additive (↥Kw)ˣ) p :=
    LinearEquiv.ofBijective (fA.toZModLinearMap p) ⟨hfA_inj, hfA_surj⟩
  have heμ : ∀ c, ((eμ c : tor (Additive (↥Kw)ˣ) p) : Additive (↥Kw)ˣ) = Additive.ofMul (ζK ^ c.val) := fun _ => rfl

  have heμ_eq : ∀ (g : Γ) (c : ZMod p),
      eμ (((Representation.trivial (ZMod p) Γ (ZMod p)).twist χΓ) g c) = ((torRep actXK).comp resK) g (eμ c) := by
    intro g c
    apply Subtype.ext
    rw [heμ]
    show Additive.ofMul (ζK ^ ((χΓ g : ZMod p) * c).val) = actXK (resK g) (eμ c : Additive (↥Kw)ˣ)
    rw [heμ, actXK_apply, MonoidHom.map_pow, hζK_act, ← pow_mul, ZMod.val_mul, hpowmod]
  have hF2a : finrank (ZMod p) (ρD.linHom ((Representation.trivial (ZMod p) Γ (ZMod p)).twist χΓ)).invariants
      = finrank (ZMod p) (ρD.linHom ((torRep actXK).comp resK)).invariants :=
    finrank_hom_eq_of_equiv ρD _ _ eμ heμ_eq
  have hF2b : finrank (ZMod p) (ρD.linHom ((Representation.trivial (ZMod p) Γ (ZMod p)).twist χΓ)).invariants
      = finrank (ZMod p) MΓ.ρ.invariants := by
    have h := Representation.finrank_invariants_linHom_dual_twist_ofChar MΓ.ρ χΓ
    exact h
  have hF2c : finrank (ZMod p) (ρD.linHom ((torRep actXK).comp resK)).invariants
      = finrank (ZMod p) (ND.linHom (torRep actXK)).invariants := by rw [hdesc]

  have hF3a : (ND.linHom (Representation.trivial (ZMod p) (Kw ≃ₐ[K] Kw) (ZMod p))).invariants
      = ND.dual.invariants := by
    ext φ
    rw [Representation.mem_invariants, Representation.mem_invariants]
    have key : ∀ δ, (ND.linHom (Representation.trivial (ZMod p) (Kw ≃ₐ[K] Kw) (ZMod p))) δ φ = ND.dual δ φ := by
      intro δ
      rw [Representation.linHom_apply, Representation.dual_apply, Module.Dual.transpose_apply]
      rfl
    simp only [key]
  have hcardΔ : IsUnit ((Fintype.card (Kw ≃ₐ[K] Kw) : ZMod p)) := by
    rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank, ← hidx]
    exact hunitS
  have hF3b : finrank (ZMod p) ND.dual.invariants = finrank (ZMod p) ND.invariants :=
    Representation.finrank_invariants_dual_of_isUnit_card hcardΔ ND
  have hF3c : ND.invariants = ρD.invariants := by
    ext v
    rw [Representation.mem_invariants, Representation.mem_invariants]
    constructor
    · intro h g; rw [← hND]; exact h _
    · intro h δ
      obtain ⟨g, rfl⟩ := hresK_surj δ
      rw [hND]; exact h g

  have hF3 : finrank (ZMod p) (ND.linHom (Representation.trivial (ZMod p) (Kw ≃ₐ[K] Kw) (ZMod p))).invariants
      = finrank (ZMod p) ρD.invariants := by
    rw [hF3a, hF3b, hF3c]
  rw [hF1] at hKw
  linarith

end S_groupCohomology_finrank_continuousH1_eq_invariants_add_dualTwist_add_finrank_mul_of_tame_intermediateField
end P2MW
export P2MW.S_groupCohomology_finrank_continuousH1_eq_invariants_add_dualTwist_add_finrank_mul_of_tame_intermediateField (solution)
