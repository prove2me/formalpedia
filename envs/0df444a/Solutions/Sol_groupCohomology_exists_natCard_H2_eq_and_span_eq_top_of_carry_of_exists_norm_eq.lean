-- Prove2me | solution 1 for groupCohomology.exists_natCard_H2_eq_and_span_eq_top_of_carry_of_exists_norm_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/525113e0-ea8c-5771-af11-26b38d64eccd

import Mathlib
import Definitions.Def_GroupCohomology_CyclicCarry
import Theorems.Thm_groupCohomology_exists_natCard_H2_eq_and_span_eq_top_of_map_res_inf_smul_eq_zero
import Theorems.Thm_groupCohomology_map_carry_H2pi_eq_smul_carry
import Theorems.Thm_groupCohomology_carry_H2pi_eq_zero_iff
import Theorems.Thm_groupCohomology_carryFun_mem_cocycles2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_exists_natCard_H2_eq_and_span_eq_top_of_carry_of_exists_norm_eq

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits groupCohomology Rep

theorem solution
    {Γ : Type} [Group Γ] [Fintype Γ] (C : Rep ℤ Γ) (S T : Subgroup Γ) [S.Normal] [T.Normal]
    [Fintype (Γ ⧸ S)] (hST : S ⊓ T = ⊥)
    (hS1 : IsZero (groupCohomology (Rep.res S.subtype C) 1))
    (hT1 : IsZero (groupCohomology (Rep.res T.subtype C) 1))
    (s : Γ ⧸ T) (hs : ∀ g : Γ ⧸ T, g ∈ Subgroup.zpowers s) (hsfin : IsOfFinOrder s)
    (t : S) (ht : ∀ g : S, g ∈ Subgroup.zpowers t) (htfin : IsOfFinOrder t)
    (n' : ℕ) (hn' : orderOf s = n') (hn : Fintype.card (Γ ⧸ S) ∣ n')
    (a₀T : C.quotientToInvariants T) (a₀ : C) (ha₀T : (@Representation.quotientToInvariants_lift ℤ Γ _ _ C.V C.hV1 C.hV2 C.ρ T _) a₀T = a₀)
    (ha₀ : ∀ g : Γ, C.ρ g a₀ = a₀)
    (hzT : carryFun s hs hsfin a₀T ∈ cocycles₂ (C.quotientToInvariants T))
    (hord : addOrderOf ((H2π (C.quotientToInvariants T)).hom ⟨carryFun s hs hsfin a₀T, hzT⟩) = n')
    (hnorm : ∃ b : C, (∑ i ∈ Finset.range (orderOf t), C.ρ ((t : Γ) ^ i) b) = (n' / Fintype.card (Γ ⧸ S)) • a₀)
    (hfin : Finite (groupCohomology (C.quotientToInvariants S) 2))
    (hle : Nat.card (groupCohomology (C.quotientToInvariants S) 2) ≤ Fintype.card (Γ ⧸ S)) :
    ∃ y : groupCohomology (C.quotientToInvariants S) 2,
      Nat.card (groupCohomology (C.quotientToInvariants S) 2) = Fintype.card (Γ ⧸ S) ∧
      Submodule.span ℤ {y} = ⊤ ∧
      (map (A := C.quotientToInvariants S) (B := C) (QuotientGroup.mk' S)
          (@Rep.ofHom ℤ Γ _ _ _ _ (C.quotientToInvariants S).hV1 C.hV1 (C.quotientToInvariants S).hV2 C.hV2 _ _ (@Representation.quotientToInvariants_lift ℤ Γ _ _ C.V C.hV1 C.hV2 C.ρ S _)) 2).hom y =
        (n' / Fintype.card (Γ ⧸ S)) •
          (map (A := C.quotientToInvariants T) (B := C) (QuotientGroup.mk' T)
            (@Rep.ofHom ℤ Γ _ _ _ _ (C.quotientToInvariants T).hV1 C.hV1 (C.quotientToInvariants T).hV2 C.hV2 _ _ (@Representation.quotientToInvariants_lift ℤ Γ _ _ C.V C.hV1 C.hV2 C.ρ T _)) 2).hom
              ((H2π (C.quotientToInvariants T)).hom ⟨carryFun s hs hsfin a₀T, hzT⟩) := by
  classical

  have hn'0 : n' ≠ 0 := by rw [← hn']; exact (hsfin.orderOf_pos).ne'

  set liftT := (@Representation.quotientToInvariants_lift ℤ Γ _ _ C.V C.hV1 C.hV2 C.ρ T _) with hliftT
  set infTφ : Rep.res (QuotientGroup.mk' T) (C.quotientToInvariants T) ⟶ C :=
    (@Rep.ofHom ℤ Γ _ _ _ _ (C.quotientToInvariants T).hV1 C.hV1 (C.quotientToInvariants T).hV2 C.hV2 _ _ (@Representation.quotientToInvariants_lift ℤ Γ _ _ C.V C.hV1 C.hV2 C.ρ T _)) with hinfTφ
  set j : S →* Γ ⧸ T := (QuotientGroup.mk' T).comp S.subtype with hj_def
  set φ' : Rep.res j (C.quotientToInvariants T) ⟶ Rep.res S.subtype C :=
    (Rep.resFunctor S.subtype).map infTφ ≫ 𝟙 (Rep.res S.subtype C) with hφ'

  have hcomp := groupCohomology.map_comp (QuotientGroup.mk' T) S.subtype infTφ (𝟙 (Rep.res S.subtype C)) 2
  have hfac : ∀ z : groupCohomology (C.quotientToInvariants T) 2,
      (map S.subtype (𝟙 (Rep.res S.subtype C)) 2).hom ((map (A := C.quotientToInvariants T) (B := C) (QuotientGroup.mk' T) infTφ 2).hom z)
        = (map j φ' 2).hom z := by
    intro z
    have := congrArg (fun F => (ModuleCat.Hom.hom F) z) hcomp
    have h__af := this.symm
    simp [ModuleCat.hom_comp, LinearMap.comp_apply] at h__af
    exact h__af

  have hj : Function.Injective j := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxT : (x : Γ) ∈ T := by
      rw [hj_def, MonoidHom.comp_apply] at hx
      exact (QuotientGroup.eq_one_iff (x : Γ)).mp hx
    have hxS : (x : Γ) ∈ S := x.2
    have : (x : Γ) ∈ S ⊓ T := Subgroup.mem_inf.mpr ⟨hxS, hxT⟩
    rw [hST, Subgroup.mem_bot] at this
    exact Subtype.ext this
  obtain ⟨z, hz⟩ := Subgroup.mem_zpowers_iff.mp (hs (j t))
  have hos : 0 < orderOf s := hsfin.orderOf_pos
  set f : ℕ := (z % (orderOf s : ℤ)).toNat with hf
  have hjt : j t = s ^ f := by
    rw [← hz, hf, ← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hos.ne')), zpow_mod_orderOf]

  have hlift_a₀T : (liftT a₀T : C) = a₀ := ha₀T
  obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective T s
  have ha : (C.quotientToInvariants T).ρ s a₀T = a₀T := by
    apply Subtype.ext
    subst hg
    show C.ρ g (a₀T : C) = (a₀T : C)
    have : (a₀T : C) = a₀ := ha₀T
    rw [this]; exact ha₀ g
  have hφ'a : φ'.hom a₀T = a₀ := by
    rw [hφ', Category.comp_id]
    exact ha₀T
  have hzb : carryFun t ht htfin (φ'.hom a₀T) ∈ cocycles₂ (Rep.res S.subtype C) := by
    rw [hφ'a]
    exact groupCohomology.carryFun_mem_cocycles2 (A := Rep.res S.subtype C) t ht htfin a₀ (ha₀ (t : Γ))
  have h3 := groupCohomology.map_carry_H2pi_eq_smul_carry j hj s hs hsfin f t hjt ht htfin
    (C.quotientToInvariants T) (Rep.res S.subtype C) φ' a₀T ha hzT hzb

  set q : ℕ := n' / Fintype.card (Γ ⧸ S) with hq
  have hzb₀ : carryFun (A := Rep.res S.subtype C) t ht htfin a₀ ∈ cocycles₂ (Rep.res S.subtype C) :=
    groupCohomology.carryFun_mem_cocycles2 (A := Rep.res S.subtype C) t ht htfin a₀ (ha₀ (t : Γ))
  have hqa : (Rep.res S.subtype C).ρ t (q • a₀) = q • a₀ := by
    rw [map_nsmul]; exact congrArg (q • ·) (ha₀ (t : Γ))
  have hzbq : carryFun (A := Rep.res S.subtype C) t ht htfin (q • a₀) ∈ cocycles₂ (Rep.res S.subtype C) :=
    groupCohomology.carryFun_mem_cocycles2 (A := Rep.res S.subtype C) t ht htfin (q • a₀) hqa
  have hcarry_nsmul : carryFun (A := Rep.res S.subtype C) t ht htfin (q • a₀) = q • carryFun (A := Rep.res S.subtype C) t ht htfin a₀ := by
    funext p
    simp only [carryFun, Pi.smul_apply, smul_ite, smul_zero]
  have hzero : (H2π (Rep.res S.subtype C)).hom ⟨carryFun (A := Rep.res S.subtype C) t ht htfin (q • a₀), hzbq⟩ = 0 := by
    rw [groupCohomology.carry_H2pi_eq_zero_iff (A := Rep.res S.subtype C) t ht htfin (q • a₀) hqa hzbq]
    obtain ⟨b, hb⟩ := hnorm
    exact ⟨b, hb⟩
  have hq_class : q • (H2π (Rep.res S.subtype C)).hom ⟨carryFun (A := Rep.res S.subtype C) t ht htfin a₀, hzb₀⟩ = 0 := by
    rw [← map_nsmul, ← hzero]
    congr 1
    exact Subtype.ext hcarry_nsmul.symm

  have h3' : (map j φ' 2).hom ((H2π (C.quotientToInvariants T)).hom ⟨carryFun s hs hsfin a₀T, hzT⟩)
      = (f / Nat.gcd (orderOf s) f) • (H2π (Rep.res S.subtype C)).hom ⟨carryFun (A := Rep.res S.subtype C) t ht htfin a₀, hzb₀⟩ := by
    rw [h3]
    congr 2
    exact Subtype.ext (by simp only [hφ'a])
  have hres : (map S.subtype (𝟙 (Rep.res S.subtype C)) 2).hom
      (q • (map (A := C.quotientToInvariants T) (B := C) (QuotientGroup.mk' T) infTφ 2).hom
        ((H2π (C.quotientToInvariants T)).hom ⟨carryFun s hs hsfin a₀T, hzT⟩)) = 0 := by
    rw [map_nsmul, hfac, h3', smul_comm, hq_class, smul_zero]

  exact groupCohomology.exists_natCard_H2_eq_and_span_eq_top_of_map_res_inf_smul_eq_zero C S T hS1 hT1 n' hn hn'0
    ((H2π (C.quotientToInvariants T)).hom ⟨carryFun s hs hsfin a₀T, hzT⟩) hord hres hfin hle

end S_groupCohomology_exists_natCard_H2_eq_and_span_eq_top_of_carry_of_exists_norm_eq
end P2MW
export P2MW.S_groupCohomology_exists_natCard_H2_eq_and_span_eq_top_of_carry_of_exists_norm_eq (solution)
