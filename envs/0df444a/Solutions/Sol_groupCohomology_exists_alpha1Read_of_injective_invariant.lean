-- Prove2me | solution 1 for groupCohomology.exists_alpha1Read_of_injective_invariant
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/667f1ac3-9b91-5534-81eb-182d5694e01e

import Mathlib
import Definitions.Def_GroupCohomology_RelationModule
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_exists_alpha1Read_of_injective_invariant
set_option autoImplicit false
open CategoryTheory groupCohomology

namespace Alpha1Read

variable {G : Type} [Group G]

lemma nsmul_H1_eq_zero (B : Rep ℤ G) (p : ℕ) (hB : ∀ b : B, p • b = 0) (y : groupCohomology B 1) : p • y = 0 := by
  induction y using H1_induction_on with | @h c =>
  have hc : p • c = 0 := Subtype.ext (funext fun g => hB (c g))
  rw [← map_nsmul, hc, map_zero]

lemma map_add_hom {A C : Rep ℤ G} (φ φ' : A ⟶ C) (n : ℕ) :
    groupCohomology.map (MonoidHom.id G) (φ + φ') n =
      groupCohomology.map (MonoidHom.id G) φ n + groupCohomology.map (MonoidHom.id G) φ' n := by
  have h1 : cochainsMap (MonoidHom.id G) (φ + φ') = cochainsMap (MonoidHom.id G) φ + cochainsMap (MonoidHom.id G) φ' :=
    (cochainsFunctor ℤ G).map_add
  unfold groupCohomology.map
  rw [h1]
  exact (HomologicalComplex.homologyFunctor _ _ n).map_add

variable (p : ℕ) [Fact p.Prime]

noncomputable def fInt : ℤ →+ AddCircle (1 : ℚ) where
  toFun k := (((k : ℚ) / (p : ℚ) : ℚ) : AddCircle (1 : ℚ))
  map_zero' := by simp
  map_add' k k' := by push_cast; rw [add_div, QuotientAddGroup.mk_add]

lemma fInt_p : fInt p (p : ℤ) = 0 := by
  have hp : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  change (((((p : ℤ) : ℚ)) / (p : ℚ) : ℚ) : AddCircle (1 : ℚ)) = 0
  rw [Int.cast_natCast, div_self hp]
  exact (AddCircle.coe_eq_zero_iff (1 : ℚ)).2 ⟨1, by simp⟩

noncomputable def psi : ZMod p →+ AddCircle (1 : ℚ) := ZMod.lift p ⟨fInt p, fInt_p p⟩

lemma psi_intCast (k : ℤ) : psi p (k : ZMod p) = (((k : ℚ) / (p : ℚ) : ℚ) : AddCircle (1 : ℚ)) :=
  ZMod.lift_coe p ⟨fInt p, fInt_p p⟩ k

lemma psi_apply (n : ZMod p) : psi p n = ((((n.val : ℚ)) / (p : ℚ) : ℚ) : AddCircle (1 : ℚ)) := by
  conv_lhs => rw [← ZMod.natCast_zmod_val n]
  rw [← Int.cast_natCast, psi_intCast, Int.cast_natCast]

lemma psi_injective : Function.Injective (psi p) := by
  rw [injective_iff_map_eq_zero]
  intro n hn
  rw [psi_apply, AddCircle.coe_eq_zero_iff] at hn
  obtain ⟨k, hk⟩ := hn
  have hp : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  rw [zsmul_eq_mul, mul_one, eq_div_iff hp] at hk
  have h2 : (k : ℤ) * p = n.val := by exact_mod_cast hk
  have hdvd : (p : ℤ) ∣ (n.val : ℤ) := Dvd.intro_left k h2
  have : (n.val : ZMod p) = 0 := by
    rw [← Int.cast_natCast, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hdvd
  rwa [ZMod.natCast_zmod_val] at this

lemma exists_psi_eq (t : AddCircle (1 : ℚ)) (ht : p • t = 0) : ∃ n : ZMod p, psi p n = t := by
  induction t using QuotientAddGroup.induction_on with | H q =>
  have h : ((p • q : ℚ) : AddCircle (1 : ℚ)) = 0 := by rw [QuotientAddGroup.mk_nsmul]; exact ht
  rw [AddCircle.coe_eq_zero_iff] at h
  obtain ⟨k, hk⟩ := h
  have hp : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  refine ⟨(k : ZMod p), ?_⟩
  rw [psi_intCast]
  congr 1
  rw [div_eq_iff hp, mul_comm]
  rw [zsmul_eq_mul, mul_one, nsmul_eq_mul] at hk
  exact hk

noncomputable def rd {Y : Type} [AddCommGroup Y] (Z : Y →+ AddCircle (1 : ℚ)) (hZ : ∀ y, p • Z y = 0) : Y →+ ZMod p where
  toFun y := (exists_psi_eq p (Z y) (hZ y)).choose
  map_zero' := psi_injective p (by rw [(exists_psi_eq p (Z 0) (hZ 0)).choose_spec, map_zero, map_zero])
  map_add' y y' := psi_injective p (by
    have e1 := (exists_psi_eq p _ (hZ (y + y'))).choose_spec
    have e2 := (exists_psi_eq p _ (hZ y)).choose_spec
    have e3 := (exists_psi_eq p _ (hZ y')).choose_spec
    rw [e1, map_add (psi p), e2, e3, map_add Z])

lemma psi_rd {Y : Type} [AddCommGroup Y] (Z : Y →+ AddCircle (1 : ℚ)) (hZ : ∀ y, p • Z y = 0) (y : Y) :
    psi p (rd p Z hZ y) = Z y := (exists_psi_eq p (Z y) (hZ y)).choose_spec

end Alpha1Read

open Alpha1Read in

theorem solution
    {G : Type} [Group G] [Finite G] (C : Rep ℤ G)
    (invG : ↥(groupCohomology C 2) →+ AddCircle (1 : ℚ)) (hinv : Function.Injective invG)
    (p : ℕ) [Fact p.Prime] (B : Rep ℤ G) [Fintype B] (hB : ∀ b : B, p • b = 0)
    (hX : (Rep.relationSeqInt B).ShortExact) :
    ∃ al : (Rep.relationModuleInt B ⟶ C) →+ (↥(groupCohomology B 1) →+ ZMod p),
      ∀ (φ : Rep.relationModuleInt B ⟶ C) (y : ↥(groupCohomology B 1)),
        invG ((groupCohomology.map (MonoidHom.id G) φ 2).hom ((groupCohomology.δ hX 1 2 rfl).hom y))
            = ((((al φ y).val : ℚ) / (p : ℚ) : ℚ) : AddCircle (1 : ℚ)) ∧
        (al φ y = 0 ↔ (groupCohomology.map (MonoidHom.id G) φ 2).hom ((groupCohomology.δ hX 1 2 rfl).hom y) = 0) := by

  let T : (Rep.relationModuleInt B ⟶ C) → ↥(groupCohomology B 1) →+ AddCircle (1 : ℚ) := fun φ =>
    invG.comp ((groupCohomology.map (MonoidHom.id G) φ 2).hom.toAddMonoidHom.comp (groupCohomology.δ hX 1 2 rfl).hom.toAddMonoidHom)
  have hT : ∀ φ y, T φ y = invG ((groupCohomology.map (MonoidHom.id G) φ 2).hom ((groupCohomology.δ hX 1 2 rfl).hom y)) :=
    fun _ _ => rfl
  have hTadd : ∀ φ φ' y, T (φ + φ') y = T φ y + T φ' y := by
    intro φ φ' y
    rw [hT, hT, hT]
    erw [map_add_hom φ φ' 2]
    erw [ModuleCat.hom_add]
    rw [LinearMap.add_apply, map_add]
    rfl

  have hTp : ∀ φ y, p • T φ y = 0 := by
    intro φ y
    rw [← map_nsmul, nsmul_H1_eq_zero B p hB y, map_zero]
  have h0 : groupCohomology.map (MonoidHom.id G) (0 : Rep.relationModuleInt B ⟶ C) 2 = 0 :=
    (groupCohomology.functor ℤ G 2).map_zero _ _
  refine ⟨{ toFun := fun φ => rd p (T φ) (hTp φ)
            map_zero' := by
              ext y
              apply psi_injective p
              rw [psi_rd, AddMonoidHom.zero_apply, map_zero, hT, h0, ModuleCat.hom_zero, LinearMap.zero_apply, map_zero]
            map_add' := fun φ φ' => by
              ext y
              apply psi_injective p
              rw [psi_rd, AddMonoidHom.add_apply, map_add, psi_rd, psi_rd, hTadd] }, fun φ y => ⟨?_, ?_⟩⟩
  · change _ = ((((rd p (T φ) (hTp φ) y).val : ℚ) / (p : ℚ) : ℚ) : AddCircle (1 : ℚ))
    rw [← psi_apply, psi_rd]
    exact (hT φ y).symm
  · change rd p (T φ) (hTp φ) y = 0 ↔ _
    constructor
    · intro h
      apply hinv
      rw [map_zero, ← hT, ← psi_rd p (T φ) (hTp φ) y, h, map_zero]
    · intro h
      apply psi_injective p
      rw [psi_rd, map_zero, hT, h, map_zero]

end S_groupCohomology_exists_alpha1Read_of_injective_invariant
end P2MW
export P2MW.S_groupCohomology_exists_alpha1Read_of_injective_invariant (solution)
