-- Prove2me | solution 1 for groupCohomology.dualLift_unipotentOn_iff_exists_cochain_eq_sub_conj
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/2c415eb8-51c3-5e2e-99a5-3945edbd9c21

import Mathlib
import Definitions.Def_GroupCohomology_TangentSpace
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_dualLift_unipotentOn_iff_exists_cochain_eq_sub_conj

set_option autoImplicit false

open groupCohomology TrivSqZeroExt
open scoped DualNumber RightActions

universe u

namespace LocATangent

section Ring

variable {A : Type u} [Ring A]

lemma dualUnit_zero_val (u : Aˣ) : (dualUnit u 0 : A[ε]) = inl (↑u : A) := by
  refine TrivSqZeroExt.ext rfl ?_
  rw [dualUnit_val_snd, zero_mul, snd_inl]

def inlUnits : Aˣ →* (A[ε])ˣ where
  toFun u := dualUnit u 0
  map_one' := dualUnit_one_zero
  map_mul' u v := by
    rw [dualUnit_mul_dualUnit, mul_zero, zero_mul, add_zero]

@[scoped simp] lemma inlUnits_apply (u : Aˣ) : inlUnits u = dualUnit u 0 := rfl

lemma dualUnit_one_inv (m : A) : (dualUnit (1 : Aˣ) m)⁻¹ = dualUnit 1 (-m) := by
  rw [inv_eq_iff_mul_eq_one, dualUnit_mul_dualUnit, mul_one, Units.val_one, one_mul, inv_one,
    Units.val_one, mul_one, neg_add_cancel, dualUnit_one_zero]

lemma conj_inl_eq_dualUnit (m : A) (u : Aˣ) :
    dualUnit (1 : Aˣ) m * dualUnit u 0 * (dualUnit (1 : Aˣ) m)⁻¹ =
      dualUnit u (m - ↑u * m * ↑u⁻¹) := by
  rw [dualUnit_one_inv, dualUnit_mul_dualUnit, dualUnit_mul_dualUnit, one_mul, mul_one]
  congr 1
  rw [Units.val_one, mul_zero, zero_mul, zero_add, mul_neg, neg_mul, neg_add_eq_sub]

def fstMonoidHom : A[ε] →* A where
  toFun := fst
  map_one' := fst_one
  map_mul' := fst_mul

def fstUnits : (A[ε])ˣ →* Aˣ := Units.map (fstMonoidHom : A[ε] →* A)

lemma val_fstUnits (w : (A[ε])ˣ) : (fstUnits w : A) = (w : A[ε]).fst := rfl

variable {G : Type u} [Group G]

lemma fstUnits_apply_of_isDualLift {ρ₀ : G →* Aˣ} {ρ : G →* (A[ε])ˣ} (hρ : IsDualLift ρ₀ ρ)
    (g : G) : fstUnits (ρ g) = ρ₀ g :=
  Units.ext (hρ g)

lemma eq_dualUnit_cochain {ρ₀ : G →* Aˣ} {ρ : G →* (A[ε])ˣ} (hρ : IsDualLift ρ₀ ρ) (g : G) :
    ρ g = dualUnit (ρ₀ g) (dualLiftToCochain ρ₀ ρ g) :=
  eq_dualUnit_of_fst_eq (hρ g)

theorem cochain_eq_of_mem_zpowers {ρ₀ : G →* Aˣ} {ρ : G →* (A[ε])ˣ} (hρ : IsDualLift ρ₀ ρ)
    {t : G} {m : A} (ht : dualLiftToCochain ρ₀ ρ t = m - ↑(ρ₀ t) * m * ↑(ρ₀ t)⁻¹)
    {g : G} (hg : ρ g ∈ Subgroup.zpowers (ρ t)) :
    dualLiftToCochain ρ₀ ρ g = m - ↑(ρ₀ g) * m * ↑(ρ₀ g)⁻¹ := by

  set w : (A[ε])ˣ := dualUnit (1 : Aˣ) m with hw
  have hρt : ρ t = w * inlUnits (ρ₀ t) * w⁻¹ := by
    rw [eq_dualUnit_cochain hρ t, ht, inlUnits_apply, conj_inl_eq_dualUnit]
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hg

  have hρg : ρ g = w * inlUnits (ρ₀ t ^ j) * w⁻¹ := by
    rw [← hj, hρt, map_zpow]
    exact (map_zpow (MulAut.conj w) (inlUnits (ρ₀ t)) j).symm

  have hfst : ρ₀ g = ρ₀ t ^ j := by
    have h1 := fstUnits_apply_of_isDualLift hρ g
    rw [hρg, map_mul, map_mul] at h1
    have h2 : fstUnits (inlUnits (ρ₀ t ^ j)) = ρ₀ t ^ j := Units.ext rfl
    have h3 : fstUnits w = 1 := Units.ext rfl
    rw [h2, map_inv, h3, one_mul, inv_one, mul_one] at h1
    exact h1.symm
  rw [← hfst, inlUnits_apply, conj_inl_eq_dualUnit] at hρg

  unfold dualLiftToCochain
  rw [hρg, dualUnit_val_snd, Units.mul_inv_cancel_right]

theorem val_sub_one_sq_eq_of_cochain_eq {ρ₀ : G →* Aˣ} {ρ : G →* (A[ε])ˣ} (hρ : IsDualLift ρ₀ ρ)
    {g : G} {m : A} (hg : dualLiftToCochain ρ₀ ρ g = m - ↑(ρ₀ g) * m * ↑(ρ₀ g)⁻¹) :
    ((ρ g : A[ε]) - 1) ^ 2 =
      (dualUnit (1 : Aˣ) m : A[ε]) * inl (((ρ₀ g : A) - 1) ^ 2) *
        (((dualUnit (1 : Aˣ) m)⁻¹ : (A[ε])ˣ) : A[ε]) := by
  set w : (A[ε])ˣ := dualUnit (1 : Aˣ) m with hw
  have hρg : ρ g = w * inlUnits (ρ₀ g) * w⁻¹ := by
    rw [eq_dualUnit_cochain hρ g, hg, inlUnits_apply, conj_inl_eq_dualUnit]
  have hval : (ρ g : A[ε]) = (w : A[ε]) * inl (ρ₀ g : A) * ((w⁻¹ : (A[ε])ˣ) : A[ε]) := by
    rw [hρg, Units.val_mul, Units.val_mul, inlUnits_apply, dualUnit_zero_val]
  have hsub : (ρ g : A[ε]) - 1 = (w : A[ε]) * (inl (ρ₀ g : A) - 1) * ((w⁻¹ : (A[ε])ˣ) : A[ε]) := by
    rw [hval, mul_sub, sub_mul, mul_one, Units.mul_inv]
  have hinl : inl (((ρ₀ g : A) - 1) ^ 2) = ((inl (ρ₀ g : A) : A[ε]) - 1) ^ 2 := by
    rw [← inl_one A, ← inl_sub, ← inl_pow]
  rw [hsub, hinl, sq, sq]
  simp only [mul_assoc, Units.inv_mul_cancel_left]

end Ring

section TwoByTwo

variable {k : Type u} [Field k] {V : Type u} [AddCommGroup V] [Module k V]

theorem exists_eq_sub_conj_of_sq_eq_zero (hV : Module.finrank k V = 2)
    (u : (Module.End k V)ˣ) (hu1 : (u : Module.End k V) ≠ 1)
    (hu2 : ((u : Module.End k V) - 1) ^ 2 = 0) (C : Module.End k V)
    (hC : ((dualUnit u C : (Module.End k V)[ε]) - 1) ^ 2 = 0) :
    ∃ m : Module.End k V, C = m - ↑u * m * ↑u⁻¹ := by
  haveI : FiniteDimensional k V := Module.finite_of_finrank_eq_succ hV
  set N : Module.End k V := (u : Module.End k V) - 1 with hN
  clear_value N
  have hu : (u : Module.End k V) = 1 + N := by rw [hN]; abel
  have hN0 : N ≠ 0 := fun h => hu1 (by rw [hu, h, add_zero])
  have hN2 : N * N = 0 := by rw [← sq]; exact hu2
  have huinv : (↑u⁻¹ : Module.End k V) = 1 - N := by
    refine Units.inv_eq_of_mul_eq_one_right ?_
    have : (1 + N) * (1 - N) = 1 - N * N := by noncomm_ring
    rw [hu, this, hN2, sub_zero]

  have hkey : N * (C * ↑u) + (C * ↑u) * N = 0 := by
    rw [hN]
    have h2 := congrArg TrivSqZeroExt.snd hC
    rw [sq, snd_mul, snd_zero] at h2
    simpa only [fst_sub, fst_one, snd_sub, snd_one, sub_zero, dualUnit_val_fst,
      dualUnit_val_snd, smul_eq_mul, op_smul_eq_mul] using h2

  obtain ⟨v, hv⟩ : ∃ v : V, N v ≠ 0 := by
    by_contra h
    push Not at h
    exact hN0 (LinearMap.ext h)
  have hli : LinearIndependent k ![N v, v] := by
    refine LinearIndependent.pair_iff.mpr fun s t hst => ?_
    have h1 : t • N v = 0 := by
      have := congrArg N hst
      rw [map_add, map_smul, map_smul, map_zero, ← Module.End.mul_apply, hN2,
        LinearMap.zero_apply, smul_zero, zero_add] at this
      exact this
    have ht : t = 0 := (smul_eq_zero.mp h1).resolve_right hv
    rw [ht, zero_smul, add_zero] at hst
    exact ⟨(smul_eq_zero.mp hst).resolve_right hv, ht⟩
  have hcard : Fintype.card (Fin 2) = Module.finrank k V := by rw [Fintype.card_fin, hV]
  set b : Module.Basis (Fin 2) k V := basisOfLinearIndependentOfCardEqFinrank hli hcard with hb
  clear_value b
  have hb0 : b 0 = N v := by
    rw [hb, coe_basisOfLinearIndependentOfCardEqFinrank]; rfl
  have hb1 : b 1 = v := by
    rw [hb, coe_basisOfLinearIndependentOfCardEqFinrank]; rfl
  have hNb0 : N (b 0) = 0 := by
    rw [hb0, ← Module.End.mul_apply, hN2, LinearMap.zero_apply]
  have hNb1 : N (b 1) = b 0 := by rw [hb1, hb0]

  set T := LinearMap.toMatrixAlgEquiv b with hT
  clear_value T
  have hTN : T N = !![0, 1; 0, 0] := by
    ext i j
    rw [hT, LinearMap.toMatrixAlgEquiv_apply]
    fin_cases i <;> fin_cases j <;> simp [hNb0, hNb1]
  have hTC : T C = !![T C 0 0, T C 0 1; T C 1 0, T C 1 1] := Matrix.eta_fin_two (T C)
  set a : k := T C 0 0 with ha
  set b' : k := T C 0 1 with hb'
  set c : k := T C 1 0 with hc
  set d : k := T C 1 1 with hd
  clear_value a b' c d
  have hM := congrArg T hkey
  rw [map_add, map_mul, map_mul, map_mul, map_mul, hu, map_add, map_one, hTN, map_zero,
    hTC, Matrix.one_fin_two] at hM
  have hc0 : c = 0 := by
    have h := Matrix.ext_iff.mpr hM 0 0
    simp only [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.zero_apply] at h
    linear_combination h
  have had : d = -a := by
    have h := Matrix.ext_iff.mpr hM 0 1
    simp only [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.zero_apply] at h
    linear_combination h - hc0

  refine ⟨T.symm !![a + b', 0; -a, 0], T.injective ?_⟩
  rw [map_sub, map_mul, map_mul, AlgEquiv.apply_symm_apply, huinv, hu, map_add, map_one, map_sub,
    map_one, hTN, hTC, hc0, had, Matrix.one_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue, Fin.zero_eta,
      Fin.mk_one] <;> ring

end TwoByTwo

section General

variable {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k V] {G : Type} [Group G]

theorem main (hV : Module.finrank k V = 2) (ρ₀ : G →* Module.End k V)
    (ρ : G →* (DualNumber (Module.End k V))ˣ) (hρ : IsDualLift ρ₀.toHomUnits ρ)
    (I : Subgroup G) (hcyc : IsCyclic (I.map ρ))
    (hne : ∃ g ∈ I, ρ₀ g ≠ 1) (hunip : ∀ g ∈ I, (ρ₀ g - 1) ^ 2 = 0) :
    (∀ g ∈ I, ((ρ g : DualNumber (Module.End k V)) - 1) ^ 2 = 0) ↔
      ∃ m : Module.End k V, ∀ g ∈ I,
        dualLiftToCochain ρ₀.toHomUnits ρ g = m - ρ₀ g * m * ρ₀ g⁻¹ := by
  set ρ₁ := ρ₀.toHomUnits with hρ₁

  have hsp : ∀ (g : G) (m : Module.End k V),
      m - ↑(ρ₁ g) * m * ↑(ρ₁ g)⁻¹ = m - ρ₀ g * m * ρ₀ g⁻¹ := by
    intro g m
    rw [← map_inv, hρ₁, MonoidHom.coe_toHomUnits, MonoidHom.coe_toHomUnits]
  constructor
  · intro hsq

    obtain ⟨g₀, hg₀⟩ := hcyc.exists_generator
    obtain ⟨t, ht, hgt⟩ := Subgroup.mem_map.mp g₀.2
    have hzp : ∀ g ∈ I, ρ g ∈ Subgroup.zpowers (ρ t) := by
      intro g hg
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hg₀ ⟨ρ g, Subgroup.mem_map_of_mem ρ hg⟩)
      refine Subgroup.mem_zpowers_iff.mpr ⟨j, ?_⟩
      have := congrArg Subtype.val hj
      rw [SubgroupClass.coe_zpow] at this
      rw [hgt]
      exact this

    have ht1 : (ρ₁ t : Module.End k V) ≠ 1 := by
      intro h1
      obtain ⟨g, hg, hg1⟩ := hne
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hzp g hg)
      have hf := congrArg fstUnits hj
      rw [map_zpow, fstUnits_apply_of_isDualLift hρ, fstUnits_apply_of_isDualLift hρ] at hf
      have h1' : ρ₁ t = 1 := Units.ext h1
      rw [h1', one_zpow] at hf
      apply hg1
      have := congrArg Units.val hf
      rw [Units.val_one, hρ₁, MonoidHom.coe_toHomUnits] at this
      exact this.symm
    have ht2 : ((ρ₁ t : Module.End k V) - 1) ^ 2 = 0 := by
      rw [hρ₁, MonoidHom.coe_toHomUnits]; exact hunip t ht
    have hCt : ((dualUnit (ρ₁ t) (dualLiftToCochain ρ₁ ρ t) :
        (Module.End k V)[ε]) - 1) ^ 2 = 0 := by
      rw [← eq_dualUnit_cochain hρ t]; exact hsq t ht
    obtain ⟨m, hm⟩ := exists_eq_sub_conj_of_sq_eq_zero hV (ρ₁ t) ht1 ht2 _ hCt
    refine ⟨m, fun g hg => ?_⟩
    rw [← hsp]
    exact cochain_eq_of_mem_zpowers hρ hm (hzp g hg)
  · rintro ⟨m, hm⟩ g hg
    have hgm := hm g hg
    rw [← hsp] at hgm
    rw [val_sub_one_sq_eq_of_cochain_eq hρ hgm, hρ₁, MonoidHom.coe_toHomUnits, hunip g hg,
      inl_zero, mul_zero, zero_mul]

end General

end LocATangent
p2m_reactivate "P2MW.S_groupCohomology_dualLift_unipotentOn_iff_exists_cochain_eq_sub_conj.LocATangent"

open groupCohomology in
theorem solution
    {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k V]
    (hV : Module.finrank k V = 2)
    {G : Type} [Group G] (ρ₀ : G →* Module.End k V)
    (ρ : G →* (DualNumber (Module.End k V))ˣ) (hρ : IsDualLift ρ₀.toHomUnits ρ)
    (I : Subgroup G) (hcyc : IsCyclic (I.map ρ))
    (hne : ∃ g ∈ I, ρ₀ g ≠ 1) (hunip : ∀ g ∈ I, (ρ₀ g - 1) ^ 2 = 0) :
    (∀ g ∈ I, ((ρ g : DualNumber (Module.End k V)) - 1) ^ 2 = 0) ↔
      ∃ m : Module.End k V, ∀ g ∈ I,
        dualLiftToCochain ρ₀.toHomUnits ρ g = m - ρ₀ g * m * ρ₀ g⁻¹ :=
  LocATangent.main hV ρ₀ ρ hρ I hcyc hne hunip

end S_groupCohomology_dualLift_unipotentOn_iff_exists_cochain_eq_sub_conj
end P2MW
export P2MW.S_groupCohomology_dualLift_unipotentOn_iff_exists_cochain_eq_sub_conj (solution)
