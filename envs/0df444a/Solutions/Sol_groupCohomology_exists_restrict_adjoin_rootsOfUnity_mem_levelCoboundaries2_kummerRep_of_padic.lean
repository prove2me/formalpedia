-- Prove2me | solution 1 for groupCohomology.exists_restrict_adjoin_rootsOfUnity_mem_levelCoboundaries2_kummerRep_of_padic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/212d9b48-81f9-574b-93ef-4693d6f581e0

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_Kummer
import Definitions.Def_GroupCohomology_ContinuousH2Map
import Theorems.Thm_groupCohomology_exists_restrict_adjoin_rootsOfUnity_mem_levelCoboundaries2_of_padic
import Theorems.Thm_groupCohomology_continuousH2Map_kummerRep_injective_and_range_iff_smul_eq_zero
import Theorems.Thm_IntermediateField_cofinal_comp_fixingSubgroupEquiv_symm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_exists_restrict_adjoin_rootsOfUnity_mem_levelCoboundaries2_kummerRep_of_padic
p2m_attr_erase "instance" "ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv JacobiSumStickelberger.instModuleZModModP WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal"
p2m_attr_erase "simp" "groupCohomology.unitsInflate₁_apply groupCohomology.unitsInflate₂_apply ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply IsLocalRing.principalUnits_zero"

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000
open CategoryTheory groupCohomology IntermediateField

namespace P2mS26R5mu
open groupCohomology IntermediateField

theorem restrict_mem_levelCoboundaries2_of_units
    {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsAlgClosed Ω]
    (p : ℕ) [Fact p.Prime]
    (r : (Ω ≃ₐ[K] Ω) →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (hlevel : ∀ E : IntermediateField K Ω, FiniteDimensional K E →
      ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
        ∀ σ : Ω ≃ₐ[K] Ω, r σ ∈ F.fixingSubgroup → σ ∈ E.fixingSubgroup)
    (hopen : ∀ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F →
      ∃ E : IntermediateField K Ω, FiniteDimensional K E ∧
        ∀ σ : Ω ≃ₐ[K] Ω, σ ∈ E.fixingSubgroup → r σ ∈ F.fixingSubgroup)
    (L : IntermediateField K Ω) [FiniteDimensional K L]
    (c : (Ω ≃ₐ[K] Ω) × (Ω ≃ₐ[K] Ω) → Kummer.kummerRep K Ω p) (hc : c ∈ levelCocycles₂ r (Kummer.kummerRep K Ω p))
    (hU : (fun g : (Ω ≃ₐ[L] Ω) × (Ω ≃ₐ[L] Ω) =>
        (MonoidHom.toAdditive (rootsOfUnity p Ω).subtype).toIntLinearMap
          (c ((L.fixingSubgroup.subtype.comp (fixingSubgroupEquiv L).symm.toMonoidHom) g.1,
              (L.fixingSubgroup.subtype.comp (fixingSubgroupEquiv L).symm.toMonoidHom) g.2)))
      ∈ levelCoboundaries₂ (r.comp (L.fixingSubgroup.subtype.comp (fixingSubgroupEquiv L).symm.toMonoidHom))
          (Rep.ofAlgebraAutOnUnits L Ω)) :
    (fun g : (Ω ≃ₐ[L] Ω) × (Ω ≃ₐ[L] Ω) =>
        c ((L.fixingSubgroup.subtype.comp (fixingSubgroupEquiv L).symm.toMonoidHom) g.1,
           (L.fixingSubgroup.subtype.comp (fixingSubgroupEquiv L).symm.toMonoidHom) g.2))
      ∈ levelCoboundaries₂ (r.comp (L.fixingSubgroup.subtype.comp (fixingSubgroupEquiv L).symm.toMonoidHom))
          (Kummer.kummerRep L Ω p) := by
  classical
  haveI : IsGalois L Ω := IsGalois.tower_top_intermediateField L
  obtain ⟨hlevelL, hopenL⟩ := IntermediateField.cofinal_comp_fixingSubgroupEquiv_symm L r hlevel hopen
  have hS0 := groupCohomology.continuousH2Map_kummerRep_injective_and_range_iff_smul_eq_zero
    (K := L) (Ω := Ω) p (r.comp (L.fixingSubgroup.subtype.comp (fixingSubgroupEquiv L).symm.toMonoidHom)) hlevelL hopenL
  obtain ⟨hinj, -⟩ := hS0

  let c' : levelCocycles₂ (r.comp (L.fixingSubgroup.subtype.comp (fixingSubgroupEquiv L).symm.toMonoidHom)) (Kummer.kummerRep L Ω p) :=
    levelCocycles₂Map (rH := r) (A := Kummer.kummerRep K Ω p) (B := Kummer.kummerRep L Ω p)
      (L.fixingSubgroup.subtype.comp (fixingSubgroupEquiv L).symm.toMonoidHom) (fun _ => rfl) LinearMap.id (fun _ _ => rfl) ⟨c, hc⟩
  have hzero : continuousH2π _ _ c' = 0 := by
    apply hinj
    rw [map_zero]
    show continuousH2π _ _ (levelCocycles₂Map
      (rH := r.comp (L.fixingSubgroup.subtype.comp (fixingSubgroupEquiv L).symm.toMonoidHom))
      (rG := r.comp (L.fixingSubgroup.subtype.comp (fixingSubgroupEquiv L).symm.toMonoidHom))
      (A := Kummer.kummerRep L Ω p) (B := Rep.ofAlgebraAutOnUnits L Ω)
      (MonoidHom.id _) (fun _ => rfl) (MonoidHom.toAdditive (rootsOfUnity p Ω).subtype).toIntLinearMap (fun _ _ => rfl) c') = 0
    rw [continuousH2π_eq_zero_iff]
    exact hU
  exact (continuousH2π_eq_zero_iff _ _ c').1 hzero

end P2mS26R5mu

theorem solution
    (q : ℕ) [Fact q.Prime] (p : ℕ) [Fact p.Prime]
    (K : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K]
    (r : (PadicAlgCl q ≃ₐ[K] PadicAlgCl q) →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (hlevel : ∀ E : IntermediateField K (PadicAlgCl q), FiniteDimensional K E →
      ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
        ∀ σ : PadicAlgCl q ≃ₐ[K] PadicAlgCl q, r σ ∈ F.fixingSubgroup → σ ∈ E.fixingSubgroup)
    (hopen : ∀ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F →
      ∃ E : IntermediateField K (PadicAlgCl q), FiniteDimensional K E ∧
        ∀ σ : PadicAlgCl q ≃ₐ[K] PadicAlgCl q, σ ∈ E.fixingSubgroup → r σ ∈ F.fixingSubgroup)
    (c : (PadicAlgCl q ≃ₐ[K] PadicAlgCl q) × (PadicAlgCl q ≃ₐ[K] PadicAlgCl q) → Kummer.kummerRep K (PadicAlgCl q) p)
    (hc : c ∈ levelCocycles₂ r (Kummer.kummerRep K (PadicAlgCl q) p)) :
    ∃ (N : ℕ) (_ : 0 < N),
      (fun g : (PadicAlgCl q ≃ₐ[IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}] PadicAlgCl q)
              × (PadicAlgCl q ≃ₐ[IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}] PadicAlgCl q) =>
          c (((IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}).fixingSubgroup.subtype.comp
                (IntermediateField.fixingSubgroupEquiv (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})).symm.toMonoidHom) g.1,
             ((IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}).fixingSubgroup.subtype.comp
                (IntermediateField.fixingSubgroupEquiv (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})).symm.toMonoidHom) g.2))
        ∈ levelCoboundaries₂
            (r.comp ((IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}).fixingSubgroup.subtype.comp
                (IntermediateField.fixingSubgroupEquiv (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})).symm.toMonoidHom))
            (Kummer.kummerRep (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) (PadicAlgCl q) p) := by
  classical
  haveI : IsGalois ℚ_[q] (PadicAlgCl q) := IsAlgClosure.isGalois ℚ_[q] (PadicAlgCl q)
  haveI : IsGalois K (PadicAlgCl q) := IsGalois.tower_top_intermediateField K

  let cU : levelCocycles₂ r (Rep.ofAlgebraAutOnUnits K (PadicAlgCl q)) :=
    levelCocycles₂Map (rH := r) (rG := r) (A := Kummer.kummerRep K (PadicAlgCl q) p) (B := Rep.ofAlgebraAutOnUnits K (PadicAlgCl q))
      (MonoidHom.id _) (fun _ => rfl) (MonoidHom.toAdditive (rootsOfUnity p (PadicAlgCl q)).subtype).toIntLinearMap
      (fun _ _ => rfl) ⟨c, hc⟩

  obtain ⟨N, hN, hcob⟩ :=
    groupCohomology.exists_restrict_adjoin_rootsOfUnity_mem_levelCoboundaries2_of_padic q K r hlevel hopen cU.1 cU.2
  refine ⟨N, hN, ?_⟩

  have hn : 0 < q ^ N - 1 := Nat.sub_pos_of_lt (Nat.one_lt_pow hN.ne' (Nat.Prime.one_lt Fact.out))
  haveI : Finite {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1} := by
    apply Set.Finite.to_subtype
    apply (Polynomial.nthRootsFinset (q ^ N - 1) (1 : PadicAlgCl q)).finite_toSet.subset
    intro ζ hζ
    simpa [Polynomial.mem_nthRootsFinset hn] using hζ
  haveI : FiniteDimensional K (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) :=
    IntermediateField.finiteDimensional_adjoin (fun ζ hζ => IsIntegral.of_pow hn
      (by rw [show ζ ^ (q ^ N - 1) = 1 from hζ]; exact isIntegral_one))
  exact P2mS26R5mu.restrict_mem_levelCoboundaries2_of_units p r hlevel hopen (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) c hc hcob

end S_groupCohomology_exists_restrict_adjoin_rootsOfUnity_mem_levelCoboundaries2_kummerRep_of_padic
end P2MW
export P2MW.S_groupCohomology_exists_restrict_adjoin_rootsOfUnity_mem_levelCoboundaries2_kummerRep_of_padic (solution)
