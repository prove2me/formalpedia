-- Prove2me | solution 1 for groupCohomology.exists_restrict_adjoin_rootsOfUnity_mem_levelCoboundaries2_of_padic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/8a04a4e3-07d8-5723-8c22-48756e7e3d1b

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_ContinuousH2Map
import Definitions.Def_GroupCohomology_GaloisUnitsInflation
import Theorems.Thm_groupCohomology_exists_mem_split_adjoin_rootsOfUnity_of_padic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_exists_restrict_adjoin_rootsOfUnity_mem_levelCoboundaries2_of_padic
p2m_attr_erase "instance" "ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv JacobiSumStickelberger.instModuleZModModP WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal"
p2m_attr_erase "simp" "ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply IsLocalRing.principalUnits_zero"

set_option autoImplicit false
p2m_open "CategoryTheory groupCohomology P2MW.S_groupCohomology_exists_restrict_adjoin_rootsOfUnity_mem_levelCoboundaries2_of_padic.groupCohomology IntermediateField"

namespace groupCohomology
p2m_export "groupCohomology" "congr d₁₂_hom_apply map isLevelConstant₁_const levelCocycles₂ levelCoboundaries₂ mem_levelCoboundaries₂_iff continuousH2π continuousH2π_eq_zero_iff cochainsPullPush₂ cochainsPullPush₂_mem_levelCoboundaries₂ unitsInflate₁ unitsInflate₂ exists_mem_split_adjoin_rootsOfUnity_of_padic"
p2m_open "groupCohomology"

section GIhelpers
variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] (L : IntermediateField K Ω)

private noncomputable def ιA : (Rep.ofAlgebraAutOnUnits K L) →+ (Rep.ofAlgebraAutOnUnits K Ω) where
  toFun b := (Additive.ofMul (Units.map (algebraMap L Ω).toMonoidHom (Additive.toMul (α := (L)ˣ) b)) :
    Additive Ωˣ)
  map_zero' := congrArg Additive.ofMul (map_one (Units.map (algebraMap L Ω).toMonoidHom))
  map_add' b b' := congrArg Additive.ofMul
    (map_mul (Units.map (algebraMap L Ω).toMonoidHom) (Additive.toMul (α := (L)ˣ) b)
      (Additive.toMul (α := (L)ˣ) b'))

private lemma coe_ιA (b : Rep.ofAlgebraAutOnUnits K L) :
    ((Additive.toMul (α := Ωˣ) (ιA L b) : Ωˣ) : Ω) = algebraMap L Ω ((Additive.toMul (α := (L)ˣ) b : (L)ˣ) : L) :=
  rfl

private lemma ιA_injective : Function.Injective (ιA L) := by
  intro b b' h
  have h' := congrArg (fun a : Rep.ofAlgebraAutOnUnits K Ω => ((Additive.toMul (α := Ωˣ) a : Ωˣ) : Ω)) h
  simp only [coe_ιA] at h'
  exact (Additive.toMul (α := (L)ˣ)).injective (Units.ext ((algebraMap L Ω).injective h'))

private lemma coe_ρΩ (g : Ω ≃ₐ[K] Ω) (a : Rep.ofAlgebraAutOnUnits K Ω) :
    ((Additive.toMul (α := Ωˣ) ((Rep.ofAlgebraAutOnUnits K Ω).ρ g a) : Ωˣ) : Ω)
      = g ((Additive.toMul (α := Ωˣ) a : Ωˣ) : Ω) := rfl

private lemma ext_Ω {a a' : Rep.ofAlgebraAutOnUnits K Ω}
    (h : ((Additive.toMul (α := Ωˣ) a : Ωˣ) : Ω) = ((Additive.toMul (α := Ωˣ) a' : Ωˣ) : Ω)) : a = a' :=
  (Additive.toMul (α := Ωˣ)).injective (Units.ext h)

variable [Normal K L]

private lemma unitsInflate₂_eq (f : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Additive (L)ˣ) (g h : Ω ≃ₐ[K] Ω) :
    unitsInflate₂ L f (g, h) = ιA L (f (AlgEquiv.restrictNormalHom L g, AlgEquiv.restrictNormalHom L h)) := rfl

private lemma unitsInflate₁_eq (c : (L ≃ₐ[K] L) → Additive (L)ˣ) (g : Ω ≃ₐ[K] Ω) :
    unitsInflate₁ L c g = ιA L (c (AlgEquiv.restrictNormalHom L g)) := rfl

private lemma ιA_ρ (g : Ω ≃ₐ[K] Ω) (b : Rep.ofAlgebraAutOnUnits K L) :
    ιA L ((Rep.ofAlgebraAutOnUnits K L).ρ (AlgEquiv.restrictNormalHom L g) b)
      = (Rep.ofAlgebraAutOnUnits K Ω).ρ g (ιA L b) :=
  ext_Ω (AlgEquiv.restrictNormal_commutes g L _)

private lemma restrictNormalHom_eq_one_iff (s : Ω ≃ₐ[K] Ω) :
    AlgEquiv.restrictNormalHom L s = 1 ↔ s ∈ L.fixingSubgroup := by
  rw [← IntermediateField.restrictNormalHom_ker L, MonoidHom.mem_ker]

end GIhelpers

end groupCohomology

namespace groupCohomology
p2m_export "groupCohomology" "congr d₁₂_hom_apply map isLevelConstant₁_const levelCocycles₂ levelCoboundaries₂ mem_levelCoboundaries₂_iff continuousH2π continuousH2π_eq_zero_iff cochainsPullPush₂ cochainsPullPush₂_mem_levelCoboundaries₂ unitsInflate₁ unitsInflate₂ exists_mem_split_adjoin_rootsOfUnity_of_padic"
p2m_open "groupCohomology"

set_option maxHeartbeats 3200000 in

private theorem restrict_mem_levelCoboundaries2_of_eq_inflate {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
    (r : (Ω ≃ₐ[K] Ω) →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (L : IntermediateField K Ω) [Normal K L]
    (c : (Ω ≃ₐ[K] Ω) × (Ω ≃ₐ[K] Ω) → Rep.ofAlgebraAutOnUnits K Ω) (hc : c ∈ levelCocycles₂ r (Rep.ofAlgebraAutOnUnits K Ω))
    (f : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Additive (L)ˣ)
    (h : unitsInflate₂ L f ∈ levelCocycles₂ r (Rep.ofAlgebraAutOnUnits K Ω))
    (e : continuousH2π r (Rep.ofAlgebraAutOnUnits K Ω) ⟨c, hc⟩ = continuousH2π r (Rep.ofAlgebraAutOnUnits K Ω) ⟨unitsInflate₂ L f, h⟩) :
    (fun g : (Ω ≃ₐ[L] Ω) × (Ω ≃ₐ[L] Ω) =>
        c ((L.fixingSubgroup.subtype.comp (IntermediateField.fixingSubgroupEquiv L).symm.toMonoidHom) g.1,
           (L.fixingSubgroup.subtype.comp (IntermediateField.fixingSubgroupEquiv L).symm.toMonoidHom) g.2))
      ∈ levelCoboundaries₂ (r.comp (L.fixingSubgroup.subtype.comp (IntermediateField.fixingSubgroupEquiv L).symm.toMonoidHom))
          (Rep.ofAlgebraAutOnUnits L Ω) := by

  have hdiff : (((⟨c, hc⟩ : levelCocycles₂ r (Rep.ofAlgebraAutOnUnits K Ω)) - ⟨unitsInflate₂ L f, h⟩
        : levelCocycles₂ r (Rep.ofAlgebraAutOnUnits K Ω)) : _ → Rep.ofAlgebraAutOnUnits K Ω)
      ∈ levelCoboundaries₂ r (Rep.ofAlgebraAutOnUnits K Ω) := by
    rw [← sub_eq_zero, ← map_sub] at e
    exact (continuousH2π_eq_zero_iff r _ _).1 e
  have hres := cochainsPullPush₂_mem_levelCoboundaries₂ (rH := r)
    (rG := r.comp (L.fixingSubgroup.subtype.comp (IntermediateField.fixingSubgroupEquiv L).symm.toMonoidHom))
    (A := Rep.ofAlgebraAutOnUnits K Ω) (B := Rep.ofAlgebraAutOnUnits L Ω)
    (L.fixingSubgroup.subtype.comp (IntermediateField.fixingSubgroupEquiv L).symm.toMonoidHom) (fun _ => rfl)
    LinearMap.id (fun _ _ => rfl) hdiff

  have hπ : ∀ g : Ω ≃ₐ[L] Ω,
      AlgEquiv.restrictNormalHom L ((L.fixingSubgroup.subtype.comp (IntermediateField.fixingSubgroupEquiv L).symm.toMonoidHom) g) = 1 := by
    intro g
    rw [← MonoidHom.mem_ker, IntermediateField.restrictNormalHom_ker]
    exact ((IntermediateField.fixingSubgroupEquiv L).symm g).2
  have hconst : (fun g : (Ω ≃ₐ[L] Ω) × (Ω ≃ₐ[L] Ω) =>
      (unitsInflate₂ L f ((L.fixingSubgroup.subtype.comp (IntermediateField.fixingSubgroupEquiv L).symm.toMonoidHom) g.1,
         (L.fixingSubgroup.subtype.comp (IntermediateField.fixingSubgroupEquiv L).symm.toMonoidHom) g.2)
        : Rep.ofAlgebraAutOnUnits L Ω))
      ∈ levelCoboundaries₂ (r.comp (L.fixingSubgroup.subtype.comp (IntermediateField.fixingSubgroupEquiv L).symm.toMonoidHom))
          (Rep.ofAlgebraAutOnUnits L Ω) := by
    refine (mem_levelCoboundaries₂_iff _ _ _).2 ⟨fun _ => ιA L (f (1, 1)), isLevelConstant₁_const _ _, funext fun g => ?_⟩
    obtain ⟨g₁, g₂⟩ := g
    rw [d₁₂_hom_apply]
    dsimp only
    rw [unitsInflate₂_eq, hπ, hπ]

    have hfix : (Rep.ofAlgebraAutOnUnits L Ω).ρ g₁ (ιA L (f (1, 1))) = ιA L (f (1, 1)) := by
      apply (Additive.toMul (α := Ωˣ)).injective
      apply Units.ext
      show g₁ ((Additive.toMul (α := Ωˣ) (ιA L (f (1, 1))) : Ωˣ) : Ω) = _
      rw [coe_ιA]
      exact g₁.commutes _
    rw [hfix, sub_add_cancel]

  have hconst' : cochainsPullPush₂ (A := Rep.ofAlgebraAutOnUnits K Ω) (B := Rep.ofAlgebraAutOnUnits L Ω)
      (L.fixingSubgroup.subtype.comp (IntermediateField.fixingSubgroupEquiv L).symm.toMonoidHom) LinearMap.id (unitsInflate₂ L f)
      ∈ levelCoboundaries₂ (r.comp (L.fixingSubgroup.subtype.comp (IntermediateField.fixingSubgroupEquiv L).symm.toMonoidHom)) (Rep.ofAlgebraAutOnUnits L Ω) := hconst
  have e2 : cochainsPullPush₂ (A := Rep.ofAlgebraAutOnUnits K Ω) (B := Rep.ofAlgebraAutOnUnits L Ω) (L.fixingSubgroup.subtype.comp (IntermediateField.fixingSubgroupEquiv L).symm.toMonoidHom) LinearMap.id c
      = cochainsPullPush₂ (A := Rep.ofAlgebraAutOnUnits K Ω) (B := Rep.ofAlgebraAutOnUnits L Ω) (L.fixingSubgroup.subtype.comp (IntermediateField.fixingSubgroupEquiv L).symm.toMonoidHom) LinearMap.id
          (((⟨c, hc⟩ : levelCocycles₂ r (Rep.ofAlgebraAutOnUnits K Ω)) - ⟨unitsInflate₂ L f, h⟩
            : levelCocycles₂ r (Rep.ofAlgebraAutOnUnits K Ω)) : _ → Rep.ofAlgebraAutOnUnits K Ω)
        + cochainsPullPush₂ (A := Rep.ofAlgebraAutOnUnits K Ω) (B := Rep.ofAlgebraAutOnUnits L Ω) (L.fixingSubgroup.subtype.comp (IntermediateField.fixingSubgroupEquiv L).symm.toMonoidHom) LinearMap.id
          (unitsInflate₂ L f) := by
    rw [← map_add]
    congr 1
    exact (sub_add_cancel _ _).symm
  have hfin : cochainsPullPush₂ (A := Rep.ofAlgebraAutOnUnits K Ω) (B := Rep.ofAlgebraAutOnUnits L Ω) (L.fixingSubgroup.subtype.comp (IntermediateField.fixingSubgroupEquiv L).symm.toMonoidHom) LinearMap.id c
      ∈ levelCoboundaries₂ (r.comp (L.fixingSubgroup.subtype.comp (IntermediateField.fixingSubgroupEquiv L).symm.toMonoidHom)) (Rep.ofAlgebraAutOnUnits L Ω) := by
    rw [e2]
    exact add_mem hres hconst'
  exact hfin

end groupCohomology

set_option maxHeartbeats 3200000 in
theorem solution
    (q : ℕ) [Fact q.Prime]
    (K : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K]
    (r : (PadicAlgCl q ≃ₐ[K] PadicAlgCl q) →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (hlevel : ∀ E : IntermediateField K (PadicAlgCl q), FiniteDimensional K E →
      ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
        ∀ σ : PadicAlgCl q ≃ₐ[K] PadicAlgCl q, r σ ∈ F.fixingSubgroup → σ ∈ E.fixingSubgroup)
    (hopen : ∀ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F →
      ∃ E : IntermediateField K (PadicAlgCl q), FiniteDimensional K E ∧
        ∀ σ : PadicAlgCl q ≃ₐ[K] PadicAlgCl q, σ ∈ E.fixingSubgroup → r σ ∈ F.fixingSubgroup)
    (c : (PadicAlgCl q ≃ₐ[K] PadicAlgCl q) × (PadicAlgCl q ≃ₐ[K] PadicAlgCl q) → Rep.ofAlgebraAutOnUnits K (PadicAlgCl q))
    (hc : c ∈ levelCocycles₂ r (Rep.ofAlgebraAutOnUnits K (PadicAlgCl q))) :
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
            (Rep.ofAlgebraAutOnUnits (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) (PadicAlgCl q)) := by
  classical

  obtain ⟨N, hN, hfd, hnorm, f, hf, h, e⟩ :=
    groupCohomology.exists_mem_split_adjoin_rootsOfUnity_of_padic q K r hlevel hopen (continuousH2π r _ ⟨c, hc⟩)
  haveI := hfd; haveI := hnorm
  refine ⟨N, hN, ?_⟩
  exact restrict_mem_levelCoboundaries2_of_eq_inflate r (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) c hc f h e

end S_groupCohomology_exists_restrict_adjoin_rootsOfUnity_mem_levelCoboundaries2_of_padic
end P2MW
export P2MW.S_groupCohomology_exists_restrict_adjoin_rootsOfUnity_mem_levelCoboundaries2_of_padic (solution)
