-- Prove2me | solution 1 for groupCohomology.finiteDimensional_and_finrank_continuousH1Sr_twist_eq_unitsModP_add_sClassTorsionP
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/b705d3ff-056f-5d9b-9975-49f0bd5d5423

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import Definitions.Def_NumberField_LevelArithmeticModP
import Theorems.Thm_groupCohomology_exists_continuousH1Sr_linearEquiv_inf_of_isTrivial_of_coprime
import Theorems.Thm_NumberField_LevelArith_finiteDimensional_and_finrank_continuousH1Sr_res_inf_eq_finrank_invariants_selmerRep_tensor
import Theorems.Thm_NumberField_LevelArith_finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP
import Theorems.Thm_ExtCitation_cycloChar_eq_one_of_mem_fixingSubgroup_of_isPrimitiveRoot_mem
import Definitions.Def_NumberField_SelmerRepModP
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_finiteDimensional_and_finrank_continuousH1Sr_twist_eq_unitsModP_add_sClassTorsionP
p2m_attr_erase "instance" "groupCohomology.Kummer.instMulDistribMulActionRootsOfUnity"
p2m_attr_erase "simp" "groupCohomology.Kummer.coe_kummerCocycleRoots groupCohomology.Kummer.mem_powerSubgroup_iff groupCohomology.Kummer.val_smul_units groupCohomology.Kummer.kummerHom_apply groupCohomology.Kummer.coe_smul_rootsOfUnity"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
p2m_open "CategoryTheory CategoryTheory.MonoidalCategory Module groupCohomology ExtCitation NumberField.LevelArith"
open scoped Classical NumberField.LevelArith

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory Module groupCohomology ExtCitation NumberField.LevelArith"
open scoped Classical NumberField.LevelArith

namespace P2mS25EqKummerParent

def invClasses {k G : Type} [CommRing k] [Group G] (A : Rep.{0} k G) (Sg : Subgroup G) :
    Submodule k (H1 (Rep.res Sg.subtype A)) where
  carrier := {x | ∃ c : cocycles₁ (Rep.res Sg.subtype A), H1π _ c = x ∧
    ∀ g : G, ∃ a : A, ∀ s t : ↥Sg, (g⁻¹ * s * g : G) = t → A.ρ g (c t) - c s = A.ρ (s : G) a - a}
  zero_mem' := ⟨0, map_zero _, fun g => ⟨0, fun s t _ => by
    change A.ρ g 0 - 0 = A.ρ (s : G) 0 - 0
    simp⟩⟩
  add_mem' := by
    rintro x y ⟨c, rfl, hc⟩ ⟨d, rfl, hd⟩
    refine ⟨c + d, map_add _ _ _, fun g => ?_⟩
    obtain ⟨a, ha⟩ := hc g
    obtain ⟨b, hb⟩ := hd g
    refine ⟨a + b, fun s t hst => ?_⟩
    have h1 := ha s t hst
    have h2 := hb s t hst
    change A.ρ g (c t + d t) - (c s + d s) = A.ρ (s : G) (a + b) - (a + b)
    rw [map_add, map_add, show A.ρ g (c t) + A.ρ g (d t) - (c s + d s) = (A.ρ g (c t) - c s) + (A.ρ g (d t) - d s) by abel,
      h1, h2]
    abel
  smul_mem' := by
    rintro r x ⟨c, rfl, hc⟩
    refine ⟨r • c, map_smul _ _ _, fun g => ?_⟩
    obtain ⟨a, ha⟩ := hc g
    refine ⟨r • a, fun s t hst => ?_⟩
    have h1 := ha s t hst
    change A.ρ g (r • c t) - r • c s = A.ρ (s : G) (r • a) - r • a
    rw [map_smul, map_smul, ← smul_sub, h1, smul_sub]

lemma mem_invClasses_iff {k G : Type} [CommRing k] [Group G] (A : Rep.{0} k G) (Sg : Subgroup G)
    (x : H1 (Rep.res Sg.subtype A)) :
    x ∈ invClasses A Sg ↔ ∃ c : cocycles₁ (Rep.res Sg.subtype A), H1π _ c = x ∧
      ∀ g : G, ∃ a : A, ∀ s t : ↥Sg, (g⁻¹ * s * g : G) = t → A.ρ g (c t) - c s = A.ρ (s : G) a - a := Iff.rfl

end P2mS25EqKummerParent

open P2mS25EqKummerParent in
theorem solution
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (K L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hK : K.IsUnramifiedOutside S) (hL : L.IsUnramifiedOutside S)
    [FiniteDimensional ℚ ↥K] [FiniteDimensional ℚ ↥L]
    (hKL : K ≤ L) [Normal ↥K ↥(levelField K L hKL)]
    (hnorm : ∀ g ∈ K.fixingSubgroup, ∀ s ∈ L.fixingSubgroup, g * s * g⁻¹ ∈ L.fixingSubgroup)
    (hcop : (L.fixingSubgroup.relIndex K.fixingSubgroup).Coprime p)
    (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p) (hζL : ζ ∈ L)
    (N : Rep.{0} (ZMod p) ↥K.fixingSubgroup) [FiniteDimensional (ZMod p) N]
    (htriv : ∀ s : ↥K.fixingSubgroup, (s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ L.fixingSubgroup → N.ρ s = 1) :
    FiniteDimensional (ZMod p)
        ↥(continuousH1Sr K.fixingSubgroup.subtype S (N.twist ((cycloChar p).comp K.fixingSubgroup.subtype))) ∧
      Module.finrank (ZMod p)
          ↥(continuousH1Sr K.fixingSubgroup.subtype S (N.twist ((cycloChar p).comp K.fixingSubgroup.subtype))) =
        Module.finrank (ZMod p) (unitsModP K L hKL S p ⊗ N : Rep.{0} (ZMod p) ↥K.fixingSubgroup).ρ.invariants +
        Module.finrank (ZMod p) (sClassTorsionP K L hKL S p ⊗ N : Rep.{0} (ZMod p) ↥K.fixingSubgroup).ρ.invariants := by

  haveI hSgN : (L.fixingSubgroup.subgroupOf K.fixingSubgroup).Normal :=
    ⟨fun s hs g => by
      rw [Subgroup.mem_subgroupOf] at hs ⊢
      simpa using hnorm g g.2 s hs⟩
  haveI hSgF : (L.fixingSubgroup.subgroupOf K.fixingSubgroup).FiniteIndex :=
    ⟨fun h0 => by
      have : L.fixingSubgroup.relIndex K.fixingSubgroup = 0 := h0
      rw [this, Nat.coprime_zero_left] at hcop
      exact (Fact.out : p.Prime).one_lt.ne' hcop⟩

  have htrivM : ∀ s : ↥K.fixingSubgroup, (s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ L.fixingSubgroup →
      (N.twist ((cycloChar p).comp K.fixingSubgroup.subtype)).ρ s = 1 := fun s hs => by
    apply LinearMap.ext
    intro v
    change (N.ρ.twist ((cycloChar p).comp K.fixingSubgroup.subtype)) s v = v
    have hc1 : cycloChar p (s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) = 1 :=
      ExtCitation.cycloChar_eq_one_of_mem_fixingSubgroup_of_isPrimitiveRoot_mem L ζ hζ hζL _ hs
    rw [Representation.twist_apply_apply, htriv s hs]
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, hc1, Units.val_one, one_smul, Module.End.one_apply]

  let V := invClasses (N.twist ((cycloChar p).comp K.fixingSubgroup.subtype)) (L.fixingSubgroup.subgroupOf K.fixingSubgroup)
  have hV := mem_invClasses_iff (N.twist ((cycloChar p).comp K.fixingSubgroup.subtype)) (L.fixingSubgroup.subgroupOf K.fixingSubgroup)

  obtain ⟨e, -⟩ := groupCohomology.exists_continuousH1Sr_linearEquiv_inf_of_isTrivial_of_coprime S K L hL hcop
    (N.twist ((cycloChar p).comp K.fixingSubgroup.subtype)) htrivM V hV

  obtain ⟨hFD, hK2⟩ := NumberField.LevelArith.finiteDimensional_and_finrank_continuousH1Sr_res_inf_eq_finrank_invariants_selmerRep_tensor
    S hpS K L hL hKL ζ hζ hζL N htriv V hV

  have hK3 := NumberField.LevelArith.finrank_invariants_selmerRep_tensor_eq_unitsModP_add_sClassTorsionP S K L hKL hnorm hcop N
  haveI := hFD
  exact ⟨Module.Finite.equiv e.symm, by rw [LinearEquiv.finrank_eq e, hK2, hK3]⟩

end S_groupCohomology_finiteDimensional_and_finrank_continuousH1Sr_twist_eq_unitsModP_add_sClassTorsionP
end P2MW
export P2MW.S_groupCohomology_finiteDimensional_and_finrank_continuousH1Sr_twist_eq_unitsModP_add_sClassTorsionP (solution)
