-- Prove2me | solution 1 for groupCohomology.unitsInflate2_carryFun_restrict_mem_levelCoboundaries2_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/a5e642f7-d8d4-5e36-bfc3-357cfd269d71

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_GaloisUnitsInflation
import Definitions.Def_GroupCohomology_CyclicCarry
import Theorems.Thm_IntermediateField_finiteDimensional_normal_adjoin_rootsOfUnity_padic
import Theorems.Thm_groupCohomology_map_carryFun_adjoin_rootsOfUnity_eq_zero_of_dvd
import Theorems.Thm_groupCohomology_unitsInflate2_restrict_sub_unitsInflate2_map_mem_levelCoboundaries2
import Theorems.Thm_groupCohomology_unitsInflate2_mem_levelCoboundaries2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_unitsInflate2_carryFun_restrict_mem_levelCoboundaries2_of_dvd
p2m_attr_erase "instance" "ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv JacobiSumStickelberger.instModuleZModModP WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete"
p2m_attr_erase "simp" "ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply IsLocalRing.principalUnits_zero"

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000
open CategoryTheory groupCohomology

set_option maxHeartbeats 32000000 in
open groupCohomology IntermediateField in
theorem solution
    (q : ℕ) [Fact q.Prime]
    (K : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K]
    (r : (PadicAlgCl q ≃ₐ[K] PadicAlgCl q) →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (hlevel : ∀ E : IntermediateField K (PadicAlgCl q), FiniteDimensional K E →
      ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
        ∀ σ : PadicAlgCl q ≃ₐ[K] PadicAlgCl q, r σ ∈ F.fixingSubgroup → σ ∈ E.fixingSubgroup)
    (N : ℕ) (hN : 0 < N)
    [FiniteDimensional K (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})] [Normal K (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})]
    (φ : (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) ≃ₐ[K] (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) (hφ : ∀ σ, σ ∈ Subgroup.zpowers φ)
    (π : ((IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}))ˣ) (hπK : ((π : (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) : PadicAlgCl q) ∈ (K : Set (PadicAlgCl q)))
    (hcoc : carryFun φ hφ (isOfFinOrder_of_finite φ) (A := Rep.ofAlgebraAutOnUnits K (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) (Additive.ofMul π)
      ∈ cocycles₂ (Rep.ofAlgebraAutOnUnits K (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})))
    (E : IntermediateField K (PadicAlgCl q)) [FiniteDimensional K E]
    (hdvd : Module.finrank K (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) ∣ Module.finrank K E) :
    (fun g : (PadicAlgCl q ≃ₐ[E] PadicAlgCl q) × (PadicAlgCl q ≃ₐ[E] PadicAlgCl q) =>
        unitsInflate₂ (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})
          (carryFun φ hφ (isOfFinOrder_of_finite φ) (A := Rep.ofAlgebraAutOnUnits K (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) (Additive.ofMul π))
          ((E.fixingSubgroup.subtype.comp (IntermediateField.fixingSubgroupEquiv E).symm.toMonoidHom) g.1, (E.fixingSubgroup.subtype.comp (IntermediateField.fixingSubgroupEquiv E).symm.toMonoidHom) g.2))
      ∈ levelCoboundaries₂ (r.comp (E.fixingSubgroup.subtype.comp (IntermediateField.fixingSubgroupEquiv E).symm.toMonoidHom)) (Rep.ofAlgebraAutOnUnits E (PadicAlgCl q)) := by
  classical

  haveI : FiniteDimensional ℚ_[q] E := Module.Finite.trans K E
  haveI : FiniteDimensional ℚ_[q] (E.restrictScalars ℚ_[q]) := (inferInstance : FiniteDimensional ℚ_[q] E)
  obtain ⟨hfdE, hnE⟩ := IntermediateField.finiteDimensional_normal_adjoin_rootsOfUnity_padic q (E.restrictScalars ℚ_[q]) N hN
  haveI : FiniteDimensional E (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) := hfdE
  haveI : Normal E (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) := hnE
  haveI : FiniteDimensional K ((IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}).restrictScalars K) := (Module.Finite.trans E (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) : FiniteDimensional K (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}))

  have hle : IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1} ≤ (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}).restrictScalars K := by
    rw [IntermediateField.adjoin_le_iff]
    intro z hz
    exact IntermediateField.subset_adjoin E _ hz
  letI : Algebra (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) := (IntermediateField.inclusion hle).toRingHom.toAlgebra
  have halg : ∀ x : (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}), ((algebraMap (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) x : (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) : PadicAlgCl q) = (x : PadicAlgCl q) := fun _ => rfl
  haveI : IsScalarTower K (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) := IsScalarTower.of_algebraMap_eq (fun x => Subtype.ext rfl)

  let j₀ : ((IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) ≃ₐ[E] (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) →* ((IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) ≃ₐ[K] (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) :=
    { toFun := fun σ => σ.restrictScalars K
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let j : ((IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) ≃ₐ[E] (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) →* ((IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) ≃ₐ[K] (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) := (AlgEquiv.restrictNormalHom (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})).comp j₀
  have hjapp : ∀ (σ : (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) ≃ₐ[E] (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) (x : (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})), algebraMap (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) (j σ x) = σ (algebraMap (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) x) := fun σ x =>
    AlgEquiv.restrictNormal_commutes (σ.restrictScalars K) (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) x
  have hj : ∀ (σ : (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) ≃ₐ[E] (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) (x : (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) (y : (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})),
      (x : PadicAlgCl q) = (y : PadicAlgCl q) → ((j σ x : (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) : PadicAlgCl q) = ((σ y : (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) : PadicAlgCl q) := by
    intro σ x y hxy
    have h2 : algebraMap (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) x = y := Subtype.ext hxy
    rw [← halg, hjapp, h2]

  let incl : ((IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}))ˣ →* ((IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}))ˣ := Units.map ((algebraMap (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) : (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) →+* (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) : (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) →* (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}))
  have hincl : ∀ (σ : (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) ≃ₐ[E] (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) (u : ((IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}))ˣ), incl ((j σ) • u) = σ • incl u := by
    intro σ u
    apply Units.ext
    show algebraMap (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) ((j σ) (u : (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}))) = σ (algebraMap (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) (u : (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})))
    exact hjapp σ u
  let ψₗ : Additive ((IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}))ˣ →ₗ[ℤ] Additive ((IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}))ˣ := (MonoidHom.toAdditive incl).toIntLinearMap
  have hψₗ : ∀ u : ((IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}))ˣ, ψₗ (Additive.ofMul u) = Additive.ofMul (incl u) := fun _ => rfl
  let ψ : Rep.res j (Rep.ofAlgebraAutOnUnits K (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) ⟶ (Rep.ofAlgebraAutOnUnits E (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) :=
    Rep.ofHom ⟨ψₗ, fun σ => LinearMap.ext fun x => by
      show ψₗ ((Representation.ofMulDistribMulAction ((IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) ≃ₐ[K] (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) ((IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}))ˣ) (j σ) x)
        = (Representation.ofMulDistribMulAction ((IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) ≃ₐ[E] (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) ((IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}))ˣ) σ (ψₗ x)
      rw [Representation.ofMulDistribMulAction_apply_apply, Representation.ofMulDistribMulAction_apply_apply]
      change Additive.ofMul (incl ((j σ) • (Additive.toMul (x : Additive ((IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}))ˣ) : ((IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}))ˣ)))
        = Additive.ofMul (σ • incl (Additive.toMul (x : Additive ((IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}))ˣ) : ((IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}))ˣ))
      rw [hincl]⟩
  have hψ : ∀ u : ((IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}))ˣ,
      (((Additive.toMul (ψ.hom (Additive.ofMul u)) : ((IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}))ˣ) : (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) : PadicAlgCl q) = ((u : (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) : PadicAlgCl q) :=
    fun _ => rfl

  have hB := groupCohomology.unitsInflate2_restrict_sub_unitsInflate2_map_mem_levelCoboundaries2 q K r E N j hj ψ hψ
    (carryFun φ hφ (isOfFinOrder_of_finite φ) (A := (Rep.ofAlgebraAutOnUnits K (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}))) (Additive.ofMul π))

  have hA := groupCohomology.map_carryFun_adjoin_rootsOfUnity_eq_zero_of_dvd q K E N hN φ hφ j hj ψ hψ π hπK hcoc hdvd
  have hcob : (fun p : ((IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) ≃ₐ[E] (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) × ((IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) ≃ₐ[E] (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) =>
      ψ.hom (carryFun φ hφ (isOfFinOrder_of_finite φ) (A := (Rep.ofAlgebraAutOnUnits K (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}))) (Additive.ofMul π) (j p.1, j p.2)))
      ∈ coboundaries₂ (Rep.ofAlgebraAutOnUnits E (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) := by
    set x : cocycles₂ (Rep.ofAlgebraAutOnUnits K (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) := ⟨carryFun φ hφ (isOfFinOrder_of_finite φ) (A := (Rep.ofAlgebraAutOnUnits K (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}))) (Additive.ofMul π), hcoc⟩ with hx
    have h0 := H2π_comp_map (A := (Rep.ofAlgebraAutOnUnits K (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}))) (B := (Rep.ofAlgebraAutOnUnits E (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}))) j ψ
    have hfunc : (groupCohomology.map j ψ 2).hom ((H2π (Rep.ofAlgebraAutOnUnits K (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}))).hom x) = (H2π (Rep.ofAlgebraAutOnUnits E (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}))).hom ((ModuleCat.Hom.hom (mapCocycles₂ j ψ)) x) := by
      change (ModuleCat.Hom.hom (H2π (Rep.ofAlgebraAutOnUnits K (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) ≫ groupCohomology.map j ψ 2)) x = (ModuleCat.Hom.hom (mapCocycles₂ j ψ ≫ H2π (Rep.ofAlgebraAutOnUnits E (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})))) x
      rw [h0]
    rw [hfunc, H2π_eq_zero_iff] at hA
    exact hA

  have hL : ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ σ : PadicAlgCl q ≃ₐ[E] PadicAlgCl q,
        (r.comp (E.fixingSubgroup.subtype.comp (IntermediateField.fixingSubgroupEquiv E).symm.toMonoidHom)) σ ∈ F.fixingSubgroup →
          σ ∈ (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}).fixingSubgroup := by
    obtain ⟨F, hF, hFσ⟩ := hlevel ((IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}).restrictScalars K) inferInstance
    refine ⟨F, hF, fun σ hσ => ?_⟩
    have h1 := hFσ ((E.fixingSubgroup.subtype.comp (IntermediateField.fixingSubgroupEquiv E).symm.toMonoidHom) σ) hσ
    rw [IntermediateField.mem_fixingSubgroup_iff] at h1 ⊢
    intro z hz
    exact h1 z hz
  have hT2 := groupCohomology.unitsInflate2_mem_levelCoboundaries2
    (r.comp (E.fixingSubgroup.subtype.comp (IntermediateField.fixingSubgroupEquiv E).symm.toMonoidHom)) (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) hL hcob

  have heq : (fun g : (PadicAlgCl q ≃ₐ[E] PadicAlgCl q) × (PadicAlgCl q ≃ₐ[E] PadicAlgCl q) =>
        unitsInflate₂ (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) (carryFun φ hφ (isOfFinOrder_of_finite φ) (A := (Rep.ofAlgebraAutOnUnits K (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}))) (Additive.ofMul π))
          ((E.fixingSubgroup.subtype.comp (IntermediateField.fixingSubgroupEquiv E).symm.toMonoidHom) g.1,
           (E.fixingSubgroup.subtype.comp (IntermediateField.fixingSubgroupEquiv E).symm.toMonoidHom) g.2))
      = (fun g : (PadicAlgCl q ≃ₐ[E] PadicAlgCl q) × (PadicAlgCl q ≃ₐ[E] PadicAlgCl q) =>
        unitsInflate₂ (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) (carryFun φ hφ (isOfFinOrder_of_finite φ) (A := (Rep.ofAlgebraAutOnUnits K (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}))) (Additive.ofMul π))
          ((E.fixingSubgroup.subtype.comp (IntermediateField.fixingSubgroupEquiv E).symm.toMonoidHom) g.1,
           (E.fixingSubgroup.subtype.comp (IntermediateField.fixingSubgroupEquiv E).symm.toMonoidHom) g.2)
        - unitsInflate₂ (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) (fun p => ψ.hom (carryFun φ hφ (isOfFinOrder_of_finite φ) (A := (Rep.ofAlgebraAutOnUnits K (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}))) (Additive.ofMul π) (j p.1, j p.2))) g)
        + unitsInflate₂ (IntermediateField.adjoin E {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) (fun p => ψ.hom (carryFun φ hφ (isOfFinOrder_of_finite φ) (A := (Rep.ofAlgebraAutOnUnits K (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}))) (Additive.ofMul π) (j p.1, j p.2))) := by
    funext g
    simp only [Pi.add_apply, sub_add_cancel]
  rw [heq]
  exact Submodule.add_mem _ hB hT2

end S_groupCohomology_unitsInflate2_carryFun_restrict_mem_levelCoboundaries2_of_dvd
end P2MW
export P2MW.S_groupCohomology_unitsInflate2_carryFun_restrict_mem_levelCoboundaries2_of_dvd (solution)
