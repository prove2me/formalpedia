-- Prove2me | solution 1 for groupCohomology.finrank_H1_res_extArithLoc_archSlot_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/e191cd0d-f154-59b9-af70-1df70752d596

import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_finrank_H1_res_extArithLoc_archSlot_eq_zero

set_option autoImplicit false
open CategoryTheory Module groupCohomology ExtCitation

universe u

section EngineC1

open Rep.FiniteCyclicGroup

variable {k : Type u} [Field k]

private theorem twnumInf_aux_finrank_h1_add_finrank
    {G : Type u} [CommGroup G] [Fintype G] (A : Rep k G) (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) [FiniteDimensional k A] :
    finrank k (groupCohomology A 1) + finrank k A
      = finrank k (LinearMap.ker A.norm.hom.toLinearMap)
        + finrank k A.ρ.invariants := by
  classical

  let πlin := ConcreteCategory.hom (groupCohomologyπOdd A g hg 1 odd_one)
  have hπsurj : Function.Surjective πlin := by
    rw [← ModuleCat.epi_iff_surjective]
    infer_instance

  have hπker : LinearMap.ker πlin =
      Submodule.comap (LinearMap.ker A.norm.hom.toLinearMap).subtype
        (LinearMap.range (A.applyAsHom g - 𝟙 A).hom.toLinearMap) := by
    ext x
    have h__af := groupCohomologyπOdd_eq_zero_iff A g hg 1 odd_one x
    simp [LinearMap.mem_ker] at h__af
    exact h__af

  have hrange_le : LinearMap.range (A.applyAsHom g - 𝟙 A).hom.toLinearMap
      ≤ LinearMap.ker A.norm.hom.toLinearMap := by
    rintro _ ⟨x, rfl⟩
    simp only [LinearMap.mem_ker]
    have hbridge : (A.applyAsHom g - 𝟙 A).hom.toLinearMap x = A.ρ g x - x := by
      simp [Rep.sub_hom, Rep.applyAsHom]
    rw [hbridge]
    show Representation.norm A.ρ (A.ρ g x - x) = 0
    rw [map_sub, Representation.norm_self_apply, sub_self]
  have h2 : finrank k (LinearMap.ker πlin) =
      finrank k (LinearMap.range (A.applyAsHom g - 𝟙 A).hom.toLinearMap) := by
    rw [hπker]
    exact (Submodule.comapSubtypeEquivOfLe hrange_le).finrank_eq
  have h1 : finrank k (LinearMap.range πlin) + finrank k (LinearMap.ker πlin)
      = finrank k (LinearMap.ker A.norm.hom.toLinearMap) :=
    LinearMap.finrank_range_add_finrank_ker _
  have h1' : finrank k (LinearMap.range πlin) = finrank k (groupCohomology A 1) := by
    rw [LinearMap.range_eq_top.2 hπsurj]
    exact finrank_top k _
  have h3 : finrank k (LinearMap.range (A.applyAsHom g - 𝟙 A).hom.toLinearMap)
      + finrank k (LinearMap.ker (A.applyAsHom g - 𝟙 A).hom.toLinearMap)
      = finrank k A :=
    LinearMap.finrank_range_add_finrank_ker _
  have h4 : LinearMap.ker (A.applyAsHom g - 𝟙 A).hom.toLinearMap = A.ρ.invariants := by
    ext x
    rw [Representation.mem_invariants_iff_of_forall_mem_zpowers A.ρ g hg x]
    have hbridge : (A.applyAsHom g - 𝟙 A).hom.toLinearMap x = A.ρ g x - x := by
      simp [Rep.sub_hom, Rep.applyAsHom]
    simp [LinearMap.mem_ker, hbridge, sub_eq_zero]
  rw [← h1', ← h4]
  omega

private theorem twnumInf_finrank_h1_eq_zero_of_card_ne_zero
    {G : Type u} [CommGroup G] [Fintype G] (A : Rep k G) (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) [FiniteDimensional k A]
    (hcard : (Fintype.card G : k) ≠ 0) :
    finrank k (groupCohomology A 1) = 0 := by
  have hB := twnumInf_aux_finrank_h1_add_finrank A g hg

  have hrangeN : LinearMap.range A.norm.hom.toLinearMap = A.ρ.invariants := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      intro h
      exact Representation.self_norm_apply A.ρ h x
    · intro x hx
      refine ⟨(Fintype.card G : k)⁻¹ • x, ?_⟩
      have hNx : Representation.norm A.ρ x = (Fintype.card G : k) • x := by
        show (∑ h : G, A.ρ h) x = (Fintype.card G : k) • x
        rw [LinearMap.sum_apply]
        rw [Finset.sum_congr rfl fun h _ => hx h]
        simp [Finset.card_univ, Nat.cast_smul_eq_nsmul]
      show Representation.norm A.ρ ((Fintype.card G : k)⁻¹ • x) = x
      rw [map_smul, hNx, smul_smul, inv_mul_cancel₀ hcard, one_smul]
  have hrn : finrank k (LinearMap.range A.norm.hom.toLinearMap)
      + finrank k (LinearMap.ker A.norm.hom.toLinearMap) = finrank k A :=
    LinearMap.finrank_range_add_finrank_ker _
  rw [hrangeN] at hrn
  omega

end EngineC1

theorem solution
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (S : Finset Nat.Primes)
    (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    [FiniteDimensional (ZMod p) M] (u : Unit) :
    finrank (ZMod p) (H1 (Rep.res (extArithLoc S (Sum.inl u)) M)) = 0 := by
  classical

  have hfin : IsOfFinOrder complexConjugation :=
    isOfFinOrder_iff_pow_eq_one.mpr ⟨2, two_pos, complexConjugation_sq⟩
  letI instFT : Fintype (extArithLocalGroups S (Sum.inl u)) :=
    Fintype.ofEquiv (Fin (orderOf complexConjugation))
      (finEquivZPowers hfin :
        Fin (orderOf complexConjugation) ≃ extArithLocalGroups S (Sum.inl u))
  haveI : IsMulCommutative (extArithLocalGroups S (Sum.inl u)) :=
    (inferInstance : IsMulCommutative ↥(Subgroup.zpowers complexConjugation))
  letI instCG : CommGroup (extArithLocalGroups S (Sum.inl u)) :=
    { (inferInstance : Group (extArithLocalGroups S (Sum.inl u))) with
      mul_comm := fun a b => IsMulCommutative.is_comm.comm a b }
  haveI : FiniteDimensional (ZMod p) (Rep.res (extArithLoc S (Sum.inl u)) M) :=
    ‹FiniteDimensional (ZMod p) M›

  let g : extArithLocalGroups S (Sum.inl u) :=
    (⟨complexConjugation, Subgroup.mem_zpowers complexConjugation⟩ :
      ↥(Subgroup.zpowers complexConjugation))
  have hg : ∀ x : extArithLocalGroups S (Sum.inl u), x ∈ Subgroup.zpowers g := by
    intro x

    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp
      (Subtype.property (show ↥(Subgroup.zpowers complexConjugation) from x))
    exact Subgroup.mem_zpowers_iff.mpr
      ⟨n, Subtype.ext ((Subgroup.coe_zpow (Subgroup.zpowers complexConjugation)
        (show ↥(Subgroup.zpowers complexConjugation) from g) n).trans hn)⟩

  have hcard : (Fintype.card (extArithLocalGroups S (Sum.inl u)) : ZMod p) ≠ 0 := by
    have hc : Fintype.card (extArithLocalGroups S (Sum.inl u)) = orderOf complexConjugation :=
      (@Fintype.card_congr (Fin (orderOf complexConjugation)) (extArithLocalGroups S (Sum.inl u))
        _ instFT (finEquivZPowers hfin)).symm.trans (Fintype.card_fin _)
    rw [hc]
    have hdvd : orderOf complexConjugation ∣ 2 := orderOf_dvd_of_pow_eq_one complexConjugation_sq
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
    · rw [h1, Nat.cast_one]; exact one_ne_zero
    · rw [h2]
      intro h
      have hp' : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by exact_mod_cast h)
      exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp hp')
  exact twnumInf_finrank_h1_eq_zero_of_card_ne_zero
    (Rep.res (extArithLoc S (Sum.inl u)) M) g hg hcard

end S_groupCohomology_finrank_H1_res_extArithLoc_archSlot_eq_zero
end P2MW
export P2MW.S_groupCohomology_finrank_H1_res_extArithLoc_archSlot_eq_zero (solution)
