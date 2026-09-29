-- Prove2me | solution 1 for groupCohomology.exists_invariant_addCircle_of_natCard_H2_eq_of_span_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/f4a53cbb-cfbb-577c-a195-83a14a05e016

import Mathlib
import Theorems.Thm_groupCohomology_nonempty_linearEquiv_of_iso_res_mulEquiv
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_exists_invariant_addCircle_of_natCard_H2_eq_of_span_eq_top

namespace InvCAlg

open AddCircle

theorem exists_addMonoidHom_addCircle_of_span_eq_top
    {A : Type*} [AddCommGroup A] (g : A) (n : ℕ) (hn : 0 < n) (hg : addOrderOf g = n)
    (hspan : ∀ x : A, x ∈ AddSubgroup.zmultiples g) :
    ∃ f : A →+ AddCircle (1 : ℚ),
      f g = (((1 : ℚ) / n : ℚ) : AddCircle (1 : ℚ)) ∧ Function.Injective f ∧
      (∀ t : AddCircle (1 : ℚ), t ∈ f.range ↔ n • t = 0) ∧
      (∀ (k : ℤ), f (k • g) = (((k : ℚ) / n : ℚ) : AddCircle (1 : ℚ))) := by
  classical

  let ψ : ℤ →+ AddCircle (1 : ℚ) :=
    { toFun := fun k => (((k : ℚ) / n : ℚ) : AddCircle (1 : ℚ))
      map_zero' := by simp
      map_add' := fun a b => by push_cast; rw [add_div, AddCircle.coe_add] }
  have hψ : ∀ k : ℤ, ψ k = (((k : ℚ) / n : ℚ) : AddCircle (1 : ℚ)) := fun k => rfl
  have hψn : ∀ k : ℤ, ψ k = 0 ↔ (n : ℤ) ∣ k := by
    intro k
    rw [hψ, AddCircle.coe_eq_zero_iff]
    constructor
    · rintro ⟨m, hm⟩
      rw [zsmul_eq_mul, mul_one] at hm
      have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
      refine ⟨m, ?_⟩
      have : (k : ℚ) = m * n := by field_simp at hm; linarith [hm]
      exact_mod_cast (by rw [this, mul_comm] : (k : ℚ) = (n : ℚ) * m)
    · rintro ⟨m, rfl⟩
      refine ⟨m, ?_⟩
      rw [zsmul_eq_mul, mul_one]
      have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
      push_cast
      field_simp

  have hrep : ∀ x : A, ∃ k : ℤ, k • g = x := fun x => AddSubgroup.mem_zmultiples_iff.mp (hspan x)
  have hker : ∀ k : ℤ, k • g = 0 ↔ (n : ℤ) ∣ k := by
    intro k
    rw [← hg]
    exact addOrderOf_dvd_iff_zsmul_eq_zero.symm
  have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have hwd : ∀ k k' : ℤ, k • g = k' • g → ψ k = ψ k' := by
    intro k k' h
    have h0 : (k - k') • g = 0 := by rw [sub_smul, h, sub_self]
    rw [hker] at h0
    rw [← sub_eq_zero, ← map_sub, hψn]
    exact h0
  let f : A →+ AddCircle (1 : ℚ) :=
    { toFun := fun x => ψ (Classical.choose (hrep x))
      map_zero' := by
        have h := Classical.choose_spec (hrep 0)
        rw [hwd _ 0 (by rw [h, zero_zsmul]), map_zero]
      map_add' := fun x y => by
        have hx := Classical.choose_spec (hrep x)
        have hy := Classical.choose_spec (hrep y)
        have hxy := Classical.choose_spec (hrep (x + y))
        rw [← map_add]
        apply hwd
        rw [hxy, add_zsmul, hx, hy] }
  have hf : ∀ k : ℤ, f (k • g) = ψ k := fun k => hwd _ _ (Classical.choose_spec (hrep (k • g)))
  refine ⟨f, ?_, ?_, ?_, ?_⟩
  · have h1 := hf 1
    rwa [one_zsmul, hψ, Int.cast_one] at h1
  · intro x y hxy
    obtain ⟨k, rfl⟩ := hrep x
    obtain ⟨k', rfl⟩ := hrep y
    rw [hf, hf, ← sub_eq_zero, ← map_sub, hψn] at hxy
    rw [← sub_eq_zero, ← sub_smul, hker]
    exact hxy
  · intro t
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨k, rfl⟩ := hrep x
      rw [hf, hψ, ← AddCircle.coe_nsmul, nsmul_eq_mul]
      rw [mul_div_cancel₀ _ hn0, AddCircle.coe_eq_zero_iff]
      exact ⟨k, by rw [zsmul_eq_mul, mul_one]⟩
    · intro ht
      obtain ⟨r, rfl⟩ : ∃ r : ℚ, (r : AddCircle (1 : ℚ)) = t := QuotientAddGroup.mk_surjective t
      rw [← AddCircle.coe_nsmul, AddCircle.coe_eq_zero_iff] at ht
      obtain ⟨m, hm⟩ := ht
      refine ⟨m • g, ?_⟩
      rw [hf, hψ]
      congr 1
      rw [zsmul_eq_mul, mul_one, nsmul_eq_mul] at hm
      field_simp
      linarith
  · intro k
    exact (hf k).trans (hψ k)

theorem apply_eq_index_smul_of_generator
    {A B : Type*} [AddCommGroup A] [AddCommGroup B] (gA : A) (gB : B) (nA nB d : ℕ) (hnA : 0 < nA) (hd : nA = nB * d)
    (fA : A →+ AddCircle (1 : ℚ)) (fB : B →+ AddCircle (1 : ℚ))
    (hfA : ∀ k : ℤ, fA (k • gA) = (((k : ℚ) / nA : ℚ) : AddCircle (1 : ℚ)))
    (hfB : ∀ k : ℤ, fB (k • gB) = (((k : ℚ) / nB : ℚ) : AddCircle (1 : ℚ)))
    (hspan : ∀ x : A, x ∈ AddSubgroup.zmultiples gA) (r : A →+ B) (hr : r gA = gB) (x : A) :
    fB (r x) = d • fA x := by
  obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp (hspan x)
  rw [map_zsmul, hr, hfB, hfA, ← AddCircle.coe_nsmul, nsmul_eq_mul]
  congr 1
  have hnB0 : nB ≠ 0 := by rintro rfl; rw [zero_mul] at hd; omega
  have hd0 : d ≠ 0 := by rintro rfl; rw [mul_zero] at hd; omega
  have hnB : (nB : ℚ) ≠ 0 := by exact_mod_cast hnB0
  have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast hd0
  rw [hd]; push_cast
  field_simp

set_option maxHeartbeats 6400000 in
open CategoryTheory in

theorem _root_.P2MW.S_groupCohomology_exists_invariant_addCircle_of_natCard_H2_eq_of_span_eq_top.solution
    {G : Type} [Group G] [Fintype G] (X : Rep ℤ G) (u : groupCohomology X 2)
    (hcard : ∀ (S : Subgroup G) [Fintype S], Nat.card (groupCohomology (Rep.res S.subtype X) 2) = Fintype.card S)
    (hspan : ∀ S : Subgroup G, Submodule.span ℤ {(groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype X)) 2).hom u} = ⊤) :
    ∃ (invG : groupCohomology X 2 →+ AddCircle (1 : ℚ))
      (inv : ∀ H : Subgroup G, groupCohomology (Rep.res H.subtype X) 2 →+ AddCircle (1 : ℚ)),
      Function.Injective invG ∧ (∀ H : Subgroup G, Function.Injective (inv H)) ∧
      (∀ t : AddCircle (1 : ℚ), t ∈ invG.range ↔ Nat.card G • t = 0) ∧
      (∀ (H : Subgroup G) (t : AddCircle (1 : ℚ)), t ∈ (inv H).range ↔ Nat.card ↥H • t = 0) ∧
      (∀ (H : Subgroup G) (x : groupCohomology X 2),
        inv H ((groupCohomology.map H.subtype (𝟙 (Rep.res H.subtype X)) 2).hom x) = H.index • invG x) ∧
      invG u = (((1 : ℚ) / (Nat.card G : ℚ) : ℚ) : AddCircle (1 : ℚ)) ∧
      (∀ H : Subgroup G, inv H ((groupCohomology.map H.subtype (𝟙 (Rep.res H.subtype X)) 2).hom u) =
        (((1 : ℚ) / (Nat.card ↥H : ℚ) : ℚ) : AddCircle (1 : ℚ))) := by
  classical

  set g : ∀ H : Subgroup G, groupCohomology (Rep.res H.subtype X) 2 :=
    fun H => (groupCohomology.map H.subtype (𝟙 (Rep.res H.subtype X)) 2).hom u with hgdef
  have hmem : ∀ (H : Subgroup G) (x : groupCohomology (Rep.res H.subtype X) 2), x ∈ AddSubgroup.zmultiples (g H) := by
    intro H x
    have hx : x ∈ Submodule.span ℤ {g H} := by rw [hgdef, hspan H]; trivial
    obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp hx
    exact AddSubgroup.mem_zmultiples_iff.mpr ⟨k, by rw [← hk]; exact (int_smul_eq_zsmul _ k (g H)).symm⟩
  have hcardH : ∀ H : Subgroup G, Nat.card (groupCohomology (Rep.res H.subtype X) 2) = Nat.card ↥H := by
    intro H; rw [hcard H, Nat.card_eq_fintype_card]
  have hposH : ∀ H : Subgroup G, 0 < Nat.card ↥H := fun H => Nat.card_pos
  have hordH : ∀ H : Subgroup G, addOrderOf (g H) = Nat.card ↥H := by
    intro H
    haveI : Finite (groupCohomology (Rep.res H.subtype X) 2) := Nat.finite_of_card_ne_zero (by rw [hcardH]; exact (hposH H).ne')
    rw [← Nat.card_zmultiples, (AddSubgroup.eq_top_iff' _).mpr (hmem H), AddSubgroup.card_top, hcardH]

  have hex := fun H : Subgroup G =>
    exists_addMonoidHom_addCircle_of_span_eq_top (g H) (Nat.card ↥H) (hposH H) (hordH H) (hmem H)
  choose inv hinv_g hinv_inj hinv_range hinv_k using hex

  obtain ⟨ψ, hψ⟩ := groupCohomology.nonempty_linearEquiv_of_iso_res_mulEquiv
    (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G) (Rep.res (⊤ : Subgroup G).subtype X) X (Iso.refl _) 2
  have hψ' : ∀ x : groupCohomology X 2,
      ψ.symm x = (groupCohomology.map (⊤ : Subgroup G).subtype (𝟙 (Rep.res (⊤ : Subgroup G).subtype X)) 2).hom x :=
    fun x => hψ x

  have hψu : ψ.symm u = g ⊤ := hψ' u
  have hmemG : ∀ x : groupCohomology X 2, x ∈ AddSubgroup.zmultiples u := by
    intro x
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp (hmem ⊤ (ψ.symm x))
    refine AddSubgroup.mem_zmultiples_iff.mpr ⟨k, ?_⟩
    apply ψ.symm.injective
    rw [map_zsmul, hψu, hk]
  have htop : Nat.card ↥(⊤ : Subgroup G) = Nat.card G := Subgroup.card_top
  have hordG : addOrderOf u = Nat.card G := by
    rw [← htop, ← hordH ⊤, ← hψu]
    exact (addOrderOf_injective ψ.symm.toLinearMap.toAddMonoidHom ψ.symm.injective u).symm
  obtain ⟨invG, hinvG_u, hinvG_inj, hinvG_range, hinvG_k⟩ :=
    exists_addMonoidHom_addCircle_of_span_eq_top u (Nat.card G) Nat.card_pos hordG hmemG
  refine ⟨invG, inv, hinvG_inj, hinv_inj, hinvG_range, hinv_range, ?_, hinvG_u, fun H => hinv_g H⟩
  intro H x
  refine apply_eq_index_smul_of_generator u (g H) (Nat.card G) (Nat.card ↥H) H.index
    Nat.card_pos (Subgroup.card_mul_index H).symm invG (inv H) hinvG_k (hinv_k H) hmemG
    (groupCohomology.map H.subtype (𝟙 (Rep.res H.subtype X)) 2).hom.toAddMonoidHom ?_ x
  rfl

end InvCAlg

end S_groupCohomology_exists_invariant_addCircle_of_natCard_H2_eq_of_span_eq_top
end P2MW
export P2MW.S_groupCohomology_exists_invariant_addCircle_of_natCard_H2_eq_of_span_eq_top (solution)
