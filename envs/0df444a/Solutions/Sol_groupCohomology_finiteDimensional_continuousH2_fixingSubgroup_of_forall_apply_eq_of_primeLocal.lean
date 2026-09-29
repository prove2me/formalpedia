-- Prove2me | solution 1 for groupCohomology.finiteDimensional_continuousH2_fixingSubgroup_of_forall_apply_eq_of_primeLocal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/ba839f14-b816-516f-bafb-e1efabee5433

import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_ContinuousH1
import Definitions.Def_GroupCohomology_Kummer
import Theorems.Thm_groupCohomology_finrank_continuousH2_eq_one_of_equiv_rootsOfUnity_of_padic
import Theorems.Thm_IntermediateField_exists_finiteDimensional_localGaloisToGlobal_fixingSubgroupEquiv_symm_le
import Theorems.Thm_IntermediateField_exists_finiteDimensional_fixingSubgroup_le_localGaloisToGlobal_fixingSubgroupEquiv_symm
import Theorems.Thm_groupCohomology_nonempty_continuous_linearEquiv_of_mulEquiv
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_finiteDimensional_continuousH2_fixingSubgroup_of_forall_apply_eq_of_primeLocal
p2m_attr_erase "instance" "ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal"
p2m_attr_erase "simp" "groupCohomology.unitsInflate₁_apply groupCohomology.unitsInflate₂_apply ExtCitation.LocalLevel.coe_smul_OO WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply IsLocalRing.principalUnits_zero"

set_option autoImplicit false
set_option maxHeartbeats 1600000
open CategoryTheory Module groupCohomology ExtCitation

theorem solution
    {p : ℕ} [Fact p.Prime] (q : Nat.Primes) [Fact (q : ℕ).Prime]
    (K : IntermediateField ℚ_[(q : ℕ)] (PadicAlgCl (q : ℕ))) [FiniteDimensional ℚ_[(q : ℕ)] K]
    (hζ : ∃ ζ : K, IsPrimitiveRoot ζ p)
    (L : Rep (ZMod p) ↥(K.fixingSubgroup : Subgroup (primeLocalGaloisGroup q)))
    (hL : ∀ (s : ↥(K.fixingSubgroup : Subgroup (primeLocalGaloisGroup q))) (x : L), L.ρ s x = x)
    (h1 : Module.finrank (ZMod p) L = 1) :
    FiniteDimensional (ZMod p)
      (continuousH2 ((primeLocalToGlobal q).comp (K.fixingSubgroup : Subgroup (primeLocalGaloisGroup q)).subtype) L) := by
  classical
  obtain ⟨ζ, hζ⟩ := hζ
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

  let eK : ↥K.fixingSubgroup ≃* (PadicAlgCl (q : ℕ) ≃ₐ[K] PadicAlgCl (q : ℕ)) := IntermediateField.fixingSubgroupEquiv K
  let rK : (PadicAlgCl (q : ℕ) ≃ₐ[K] PadicAlgCl (q : ℕ)) →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :=
    (localGaloisToGlobal (q : ℕ)).comp (K.fixingSubgroup.subtype.comp (IntermediateField.fixingSubgroupEquiv K).symm.toMonoidHom)

  let M : Rep (ZMod p) (PadicAlgCl (q : ℕ) ≃ₐ[K] PadicAlgCl (q : ℕ)) := Rep.res eK.symm.toMonoidHom L
  have hM : ∀ (σ : PadicAlgCl (q : ℕ) ≃ₐ[K] PadicAlgCl (q : ℕ)) (m : M), M.ρ σ m = m := fun σ m => hL (eK.symm σ) m

  have hζΩ : IsPrimitiveRoot ((ζ : K) : PadicAlgCl (q : ℕ)) p := IsPrimitiveRoot.coe_submonoidClass_iff.2 hζ
  let ζu : (PadicAlgCl (q : ℕ))ˣ := (hζΩ.isUnit (NeZero.ne p)).unit
  have hζu : IsPrimitiveRoot ζu p := hζΩ.isUnit_unit (NeZero.ne p)

  haveI : Module.Finite (ZMod p) L := Module.finite_of_finrank_eq_succ h1
  let eL : L ≃ₗ[ZMod p] ZMod p := LinearEquiv.ofFinrankEq L (ZMod p) (by rw [h1, Module.finrank_self])
  let eμ : ZMod p ≃+ Additive (rootsOfUnity p (PadicAlgCl (q : ℕ))) :=
    hζu.zmodEquivZPowers.trans (MulEquiv.toAdditive (MulEquiv.subgroupCongr hζu.zpowers_eq))
  let e : M ≃+ Additive (rootsOfUnity p (PadicAlgCl (q : ℕ))) := eL.toAddEquiv.trans eμ

  have hζufix := fun σ : PadicAlgCl (q : ℕ) ≃ₐ[K] PadicAlgCl (q : ℕ) =>
    groupCohomology.Kummer.smul_units_eq_self_of_mem_range (K := K) σ (α := ζu) ⟨ζ, (IsUnit.unit_spec _).symm⟩
  have hfix : ∀ (σ : PadicAlgCl (q : ℕ) ≃ₐ[K] PadicAlgCl (q : ℕ)) (x : rootsOfUnity p (PadicAlgCl (q : ℕ))), (σ • x : rootsOfUnity p (PadicAlgCl (q : ℕ))) = x := by
    intro σ x
    apply Subtype.ext
    rw [groupCohomology.Kummer.coe_smul_rootsOfUnity]
    have hx : (x : (PadicAlgCl (q : ℕ))ˣ) ∈ Subgroup.zpowers ζu := by rw [hζu.zpowers_eq]; exact x.2
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 hx
    rw [← hi, smul_zpow', hζufix]
  have he : ∀ (σ : PadicAlgCl (q : ℕ) ≃ₐ[K] PadicAlgCl (q : ℕ)) (m : M),
      Additive.toMul (e (M.ρ σ m)) = σ • Additive.toMul (e m) := fun σ m => by rw [hM, hfix]

  obtain ⟨hfin, -⟩ := groupCohomology.finrank_continuousH2_eq_one_of_equiv_rootsOfUnity_of_padic (q : ℕ) K rK
    (fun E hE => by
      haveI := hE
      exact IntermediateField.exists_finiteDimensional_localGaloisToGlobal_fixingSubgroupEquiv_symm_le (q : ℕ) K E)
    (fun F hF => by
      haveI := hF
      exact IntermediateField.exists_finiteDimensional_fixingSubgroup_le_localGaloisToGlobal_fixingSubgroupEquiv_symm (q : ℕ) K F)
    p M e he

  obtain ⟨-, -, ⟨eH⟩⟩ := groupCohomology.nonempty_continuous_linearEquiv_of_mulEquiv rK
    ((primeLocalToGlobal q).comp (K.fixingSubgroup : Subgroup (primeLocalGaloisGroup q)).subtype)
    eK.symm (fun _ => rfl) M L (LinearEquiv.refl (ZMod p) L) (fun _ _ => rfl)
  haveI := hfin
  exact Module.Finite.equiv eH

end S_groupCohomology_finiteDimensional_continuousH2_fixingSubgroup_of_forall_apply_eq_of_primeLocal
end P2MW
export P2MW.S_groupCohomology_finiteDimensional_continuousH2_fixingSubgroup_of_forall_apply_eq_of_primeLocal (solution)
