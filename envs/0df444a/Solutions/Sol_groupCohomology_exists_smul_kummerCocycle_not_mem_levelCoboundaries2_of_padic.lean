-- Prove2me | solution 1 for groupCohomology.exists_smul_kummerCocycle_not_mem_levelCoboundaries2_of_padic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/8e5068bc-cbc5-5d5d-994e-9746146d05ed

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_Kummer

import Theorems.Thm_groupCohomology_exists_intermediateField_mem_fixingSubgroup_iff_apply_eq_zero
import Theorems.Thm_IntermediateField_exists_forall_norm_ne_of_isCyclic_padic
import Theorems.Thm_groupCohomology_smul_kummerCocycle_mem_levelCoboundaries2_iff_exists_norm_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_exists_smul_kummerCocycle_not_mem_levelCoboundaries2_of_padic
p2m_attr_erase "instance" "ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv JacobiSumStickelberger.instModuleZModModP WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete"
p2m_attr_erase "simp" "ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply IsLocalRing.principalUnits_zero groupCohomology.cochainsPullPush₁_apply groupCohomology.cochainsPullPush₂_apply groupCohomology.coe_levelCocycles₂Map groupCohomology.continuousH2Map_continuousH2π groupCohomology.unitsInflate₁_apply groupCohomology.unitsInflate₂_apply"

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000
open CategoryTheory

open groupCohomology

theorem solution
    (q : ℕ) [Fact q.Prime]
    (K : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K]
    (p : ℕ) [Fact p.Prime]
    (r : (PadicAlgCl q ≃ₐ[K] PadicAlgCl q) →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (hlevel : ∀ E : IntermediateField K (PadicAlgCl q), FiniteDimensional K E →
      ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
        ∀ σ : PadicAlgCl q ≃ₐ[K] PadicAlgCl q, r σ ∈ F.fixingSubgroup → σ ∈ E.fixingSubgroup)
    (hopen : ∀ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F →
      ∃ E : IntermediateField K (PadicAlgCl q), FiniteDimensional K E ∧
        ∀ σ : PadicAlgCl q ≃ₐ[K] PadicAlgCl q, σ ∈ E.fixingSubgroup → r σ ∈ F.fixingSubgroup)
    (χ : (PadicAlgCl q ≃ₐ[K] PadicAlgCl q) → ZMod p) (hχ : ∀ σ τ, χ (σ * τ) = χ σ + χ τ)
    (hχlc : IsLevelConstant₁ r χ) (hχ0 : ∃ σ, χ σ ≠ 0) :
    ∃ (a : (↥K)ˣ) (α : (PadicAlgCl q)ˣ) (hα : algebraMap K (PadicAlgCl q) (a : K) = (α : PadicAlgCl q) ^ p),
      (fun g : (PadicAlgCl q ≃ₐ[K] PadicAlgCl q) × (PadicAlgCl q ≃ₐ[K] PadicAlgCl q) =>
          ((χ g.1).val : ℤ) • (Kummer.kummerRep K (PadicAlgCl q) p).ρ g.1
            (Additive.ofMul (Kummer.kummerCocycleRoots hα g.2)))
        ∉ levelCoboundaries₂ r (Kummer.kummerRep K (PadicAlgCl q) p) := by
  classical
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩

  obtain ⟨E, hEfd, hEgal, hEp, hEker⟩ :=
    groupCohomology.exists_intermediateField_mem_fixingSubgroup_iff_apply_eq_zero p r hopen χ hχ hχlc hχ0
  haveI := hEfd; haveI := hEgal
  have hcyc : IsCyclic (E ≃ₐ[K] E) :=
    isCyclic_of_prime_card (p := p) (by rw [IsGalois.card_aut_eq_finrank, hEp])
  have hE1 : Module.finrank K E ≠ 1 := by rw [hEp]; exact hp.one_lt.ne'

  obtain ⟨a, ha⟩ := IntermediateField.exists_forall_norm_ne_of_isCyclic_padic q K E hcyc hE1
  obtain ⟨α, hαp⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap K (PadicAlgCl q) (a : K)) hp.pos
  have hα0 : α ≠ 0 := by
    intro h
    rw [h, zero_pow hp.ne_zero, eq_comm, map_eq_zero] at hαp
    exact a.ne_zero hαp
  refine ⟨a, Units.mk0 α hα0, by rw [Units.val_mk0, hαp], fun hmem => ?_⟩

  have hdvd : ∀ σ, (p : ℤ) ∣ ((χ σ).val : ℤ) ↔ χ σ = 0 := fun σ => by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_natCast, ZMod.natCast_zmod_val]
  obtain ⟨w, hw⟩ := (groupCohomology.smul_kummerCocycle_mem_levelCoboundaries2_iff_exists_norm_eq p r hlevel hopen
    (fun σ => ((χ σ).val : ℤ)) (hχlc.comp (fun x : ZMod p => (x.val : ℤ)))
    (fun σ τ => by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, hχ, sub_self])
    E (fun σ => (hEker σ).trans (hdvd σ).symm)
    (hχ0.imp fun σ hσ => fun h => hσ ((hdvd σ).1 h))
    a (Units.mk0 α hα0) (by rw [Units.val_mk0, hαp])).1 hmem
  exact ha w hw

end S_groupCohomology_exists_smul_kummerCocycle_not_mem_levelCoboundaries2_of_padic
end P2MW
export P2MW.S_groupCohomology_exists_smul_kummerCocycle_not_mem_levelCoboundaries2_of_padic (solution)
