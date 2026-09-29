-- Prove2me | solution 1 for groupCohomology.exists_kummerBrauer_maps_continuousH2Sr_cyclotomic_natural
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/3e057e3c-7ea2-5d04-8c52-c0b29143e55d

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_NumberField_SelmerRepModP
import Definitions.Def_NumberField_SUnitsMax
import Theorems.Thm_groupCohomology_exists_kummer_connecting_maps_continuousHSr_of_smooth_of_divisible
import Theorems.Thm_NumberField_LevelArith_nonempty_repTorsionP_sUnitsMaxRep_iso_trivial_twist_cycloChar
import Theorems.Thm_groupCohomology_exists_natural_localInv_torsionBy_continuousH2Sr_sUnitsMax
import Theorems.Thm_NumberField_LevelArith_sUnitsMaxRep_smooth_and_divisible
import Theorems.Thm_NumberField_LevelArith_sUnitsMaxStable_eq_sUnitsMax
import Theorems.Thm_IntermediateField_IsUnramifiedOutside_normalClosure
import Definitions.Def_NumberField_SUnitsMax
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_exists_kummerBrauer_maps_continuousH2Sr_cyclotomic_natural
p2m_attr_erase "instance" "M4aHerbrand.isMulCommutative_ideleClassGroup M4aHerbrand.isMulCommutative_sIdeleClassGroup ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete groupCohomology.normal_comap_fixingSubgroup groupCohomology.finiteIndex_comap_fixingSubgroup AlgebraicClosure.Rat.isGalois FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap NumberField.AdelicHaar.locallyCompactSpace_adeleRing NumberField.AdelicHaar.finite_residueField_adicCompletionIntegers NumberField.AdelicHaar.locallyCompactSpace_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_finiteAdeleRing NumberField.AdelicHaar.compactSpace_adicCompletionIntegers NumberField.AdelicHaar.t2Space_finiteAdeleRing NumberField.AdelicHaar.t2Space_matrix_adeleRing NumberField.AdelicHaar.t2Space_adeleRing NumberField.AdelicHaar.fact_isOpen_adicCompletionIntegers NumberField.AdelicHaar.t2Space_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_matrix_adeleRing NumberField.AdelicHaar.t2Space_infiniteAdeleRing NumberField.AdelicHaar.properSpace_adicCompletion ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal"
p2m_attr_erase "instance" "M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal LanglandsTunnell.P2.Artin.primeAbove_finite Deep.NTSupply.instNormalRayClassSubgroup instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal"
p2m_attr_erase "simp" "M4aHerbrand.IdeleGaloisDescent.sClassAct_mk M4aHerbrand.SIdeleClassGroup.ofLE_mk M4aHerbrand.repHomOfMulEquivariant_hom_apply M4aHerbrand.coe_finPart_apply M4aHerbrand.SIdeleClassGroup.ofLE_toSIdeleClass M4aHerbrand.IdeleGaloisDescent.sClassAct_toSIdeleClass M4aHerbrand.coe_infPart_apply M4aHerbrand.toSIdeleClass_mk M4aHerbrand.IdeleGaloisDescent.classAct_mk M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq ExtCitation.LocalLevel.coe_smul_OO WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply groupCohomology.continuousH2Inflation_H2π groupCohomology.levelInflate₂_apply groupCohomology.coe_levelInflateCocycles₂ groupCohomology.levelInflate₁_apply M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply"
p2m_attr_erase "simp" "SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff"
p2m_attr_erase "simp" "RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl IsLocalRing.principalUnits_zero groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul"
p2m_attr_erase "simp" "M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply M4aHerbrand.Bridge.finiteConorm_apply M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
p2m_open "CategoryTheory CategoryTheory.MonoidalCategory Module CategoryTheory.Limits CategoryTheory.MonoidalCategory.Limits groupCohomology ExtCitation NumberField.LevelArith"
open scoped Classical NumberField.LevelArith TensorProduct Pointwise

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
p2m_open "CategoryTheory CategoryTheory.MonoidalCategory Module CategoryTheory.Limits CategoryTheory.MonoidalCategory.Limits groupCohomology ExtCitation NumberField.LevelArith"
open scoped Classical NumberField.LevelArith TensorProduct Pointwise

set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace P2mS25EqBrauerLEq
open NumberField.LevelArith

local notation "Γ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
local notation "Qbar" => (AlgebraicClosure ℚ)

variable {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (L : IntermediateField ℚ (AlgebraicClosure ℚ))

lemma val_pow_p_eq_one_of_torsion (x : sUnitsMaxRep S L) (hx : (p : ℤ) • x = 0) : (sUnitsMaxRep.val S L x) ^ p = 1 := by
  have h1 : (((p : ℤ) • x : sUnitsMaxRep S L).1 : Additive (AlgebraicClosure ℚ)ˣ) = (p : ℤ) • (x.1 : Additive (AlgebraicClosure ℚ)ˣ) := rfl
  rw [hx] at h1
  have h2 : (p : ℕ) • (x.1 : Additive (AlgebraicClosure ℚ)ˣ) = 0 := by
    rw [← natCast_zsmul, ← h1]; rfl
  exact congrArg Additive.toMul h2

lemma val_mem_rootsOfUnity (x : sUnitsMaxRep S L) (hx : (p : ℤ) • x = 0) : sUnitsMaxRep.val S L x ∈ rootsOfUnity p Qbar :=
  (mem_rootsOfUnity _ _).2 (val_pow_p_eq_one_of_torsion S L x hx)

lemma smul_val_eq_pow_cycloChar (σ : Γ) (x : sUnitsMaxRep S L) (hx : (p : ℤ) • x = 0) :
    σ • sUnitsMaxRep.val S L x = (sUnitsMaxRep.val S L x) ^ ((cycloChar p σ : (ZMod p)ˣ) : ZMod p).val := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  apply Units.ext
  rw [Units.val_pow_eq_pow_val]
  have := modularCyclotomicCharacter.spec Qbar (card_rootsOfUnity_eq_self p) (σ : Qbar ≃+* Qbar) (val_mem_rootsOfUnity S L x hx)
  exact this

end P2mS25EqBrauerLEq

noncomputable section
namespace P2mS25EqBrauerLEq
open NumberField.LevelArith

local notation "Γ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
local notation "Qbar" => (AlgebraicClosure ℚ)

variable {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (L : IntermediateField ℚ (AlgebraicClosure ℚ))
variable (p)

abbrev rL := L.fixingSubgroup.subtype
abbrev E : Rep.{0} ℤ ↥L.fixingSubgroup := sUnitsMaxRep S L
abbrev T : Rep.{0} (ZMod p) ↥L.fixingSubgroup := repTorsionP p (E S L)
abbrev Bμ : Rep.{0} (ZMod p) ↥L.fixingSubgroup := (Rep.trivial (ZMod p) ↥L.fixingSubgroup (ZMod p)).twist ((cycloChar p).comp L.fixingSubgroup.subtype)
abbrev H2T := continuousH2Sr (rL L) S (T p S L)
abbrev H2B := continuousH2Sr (rL L) S (Bμ p L)
abbrev H2E := continuousH2Sr (rL L) S (E S L)
abbrev H1E := ↥(continuousH1Sr (rL L) S (E S L))

abbrev Hf (φ : T p S L ≅ Bμ p L) : H2T p S L →ₗ[ZMod p] H2B p S L := continuousH2SrMapHom S (rL L) φ.hom
abbrev Hg (φ : T p S L ≅ Bμ p L) : H2B p S L →ₗ[ZMod p] H2T p S L := continuousH2SrMapHom S (rL L) φ.inv

lemma Hg_Hf (φ : T p S L ≅ Bμ p L) (v : H2T p S L) : Hg p S L φ (Hf p S L φ v) = v := by
  change (continuousH2SrMapHom S (rL L) φ.inv ∘ₗ continuousH2SrMapHom S (rL L) φ.hom) v = v
  rw [← continuousH2SrMapHom_comp, Iso.hom_inv_id, continuousH2SrMapHom_id, LinearMap.id_apply]

lemma Hf_Hg (φ : T p S L ≅ Bμ p L) (y : H2B p S L) : Hf p S L φ (Hg p S L φ y) = y := by
  change (continuousH2SrMapHom S (rL L) φ.hom ∘ₗ continuousH2SrMapHom S (rL L) φ.inv) y = y
  rw [← continuousH2SrMapHom_comp, Iso.inv_hom_id, continuousH2SrMapHom_id, LinearMap.id_apply]

lemma p_nsmul_eq_zero {M : Type} [AddCommGroup M] [Module (ZMod p) M] (m : M) : p • m = 0 := by
  rw [← Nat.cast_smul_eq_nsmul (ZMod p), ZMod.natCast_self, zero_smul]

end P2mS25EqBrauerLEq
end

noncomputable section
namespace P2mS25EqBrauerLEq
open NumberField.LevelArith

local notation "Γ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
local notation "Qbar" => (AlgebraicClosure ℚ)

variable {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (L : IntermediateField ℚ (AlgebraicClosure ℚ))
variable (p)

section Core

variable (δ : H1E S L →+ H2T p S L) (ιE : H2T p S L →+ H2E S L) (φ : T p S L ≅ Bμ p L)

def ιmap : (H1E S L ⧸ ((p : ℤ) • (⊤ : Submodule ℤ (H1E S L)))) →ₗ[ZMod p] H2B p S L :=
  ((((p : ℤ) • (⊤ : Submodule ℤ (H1E S L))).liftQ
      (((Hf p S L φ).toAddMonoidHom.comp δ).toIntLinearMap) (by
        rintro _ ⟨y, -, rfl⟩
        rw [LinearMap.mem_ker]
        change Hf p S L φ (δ ((p : ℤ) • y)) = 0
        rw [natCast_zsmul, map_nsmul, map_nsmul, p_nsmul_eq_zero])).toAddMonoidHom).toZModLinearMap p

lemma ιmap_mk (x : H1E S L) : ιmap p S L δ φ (Submodule.Quotient.mk x) = Hf p S L φ (δ x) := rfl

variable (hιrange : ∀ w : H2E S L, (∃ v, ιE v = w) ↔ p • w = 0)

lemma ιE_mem_torsionBy (hιrange : ∀ w : H2E S L, (∃ v, ιE v = w) ↔ p • w = 0) (y : H2B p S L) :
    ιE (Hg p S L φ y) ∈ Submodule.torsionBy ℤ (H2E S L) (p : ℤ) := by
  rw [Submodule.mem_torsionBy_iff]
  change (p : ℤ) • ιE (Hg p S L φ y) = 0
  rw [natCast_zsmul]
  exact (hιrange _).1 ⟨_, rfl⟩

variable (invS : ↥(Submodule.torsionBy ℤ (H2E S L) (p : ℤ)) →ₗ[ZMod p] (↥(placesOverPrimes ↥L (S : Set Nat.Primes)) → ZMod p))

def κmap (hιrange : ∀ w : H2E S L, (∃ v, ιE v = w) ↔ p • w = 0) : H2B p S L →+ ↥(Submodule.torsionBy ℤ (H2E S L) (p : ℤ)) :=
  (ιE.comp (Hg p S L φ).toAddMonoidHom).codRestrict (Submodule.torsionBy ℤ (H2E S L) (p : ℤ))
    (fun y => ιE_mem_torsionBy p S L ιE φ hιrange y)

lemma κmap_apply_coe (hιrange : ∀ w : H2E S L, (∃ v, ιE v = w) ↔ p • w = 0) (y : H2B p S L) :
    ((κmap p S L ιE φ hιrange y : ↥(Submodule.torsionBy ℤ (H2E S L) (p : ℤ))) : H2E S L) = ιE (Hg p S L φ y) := rfl

def invmap (hιrange : ∀ w : H2E S L, (∃ v, ιE v = w) ↔ p • w = 0) :
    H2B p S L →ₗ[ZMod p] (↥(placesOverPrimes ↥L (S : Set Nat.Primes)) → ZMod p) :=
  (invS.toAddMonoidHom.comp (κmap p S L ιE φ hιrange)).toZModLinearMap p

lemma invmap_apply (hιrange : ∀ w : H2E S L, (∃ v, ιE v = w) ↔ p • w = 0) (y : H2B p S L) :
    invmap p S L ιE φ invS hιrange y = invS (κmap p S L ιE φ hιrange y) := rfl

lemma ιmap_injective (hδker : ∀ x : H1E S L, δ x = 0 ↔ ∃ y : H1E S L, x = p • y) : Function.Injective (ιmap p S L δ φ) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    rw [ιmap_mk] at hx
    have hx' : δ x = 0 := by rw [← Hg_Hf p S L φ (δ x), hx, map_zero]
    rw [hδker] at hx'
    obtain ⟨y, rfl⟩ := hx'
    rw [Submodule.Quotient.mk_eq_zero, ← natCast_zsmul]
    exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top

lemma range_ιmap_le_ker (hιker : ∀ v : H2T p S L, ιE v = 0 ↔ ∃ x, δ x = v)
    (hιrange : ∀ w : H2E S L, (∃ v, ιE v = w) ↔ p • w = 0) :
    LinearMap.range (ιmap p S L δ φ) ≤ LinearMap.ker (invmap p S L ιE φ invS hιrange) := by
  rintro _ ⟨x, rfl⟩
  have hκ : κmap p S L ιE φ hιrange (ιmap p S L δ φ x) = 0 := by
    induction x using Submodule.Quotient.induction_on with
    | H x =>
      have e1 := κmap_apply_coe p S L ιE φ hιrange (ιmap p S L δ φ (Submodule.Quotient.mk x))
      have e2 := congrArg (fun v => ιE (Hg p S L φ v)) (ιmap_mk p S L δ φ x)
      have e3 := congrArg ιE (Hg_Hf p S L φ (δ x))
      exact Subtype.ext (e1.trans (e2.trans (e3.trans ((hιker _).2 ⟨x, rfl⟩))))
  rw [LinearMap.mem_ker, invmap_apply, hκ, map_zero]

lemma ker_le_range_ιmap (hιker : ∀ v : H2T p S L, ιE v = 0 ↔ ∃ x, δ x = v)
    (hιrange : ∀ w : H2E S L, (∃ v, ιE v = w) ↔ p • w = 0) (hinvS : Function.Injective invS) :
    LinearMap.ker (invmap p S L ιE φ invS hιrange) ≤ LinearMap.range (ιmap p S L δ φ) := by
  intro y hy
  rw [LinearMap.mem_ker, invmap_apply] at hy
  have hy0 : κmap p S L ιE φ hιrange y = 0 := hinvS (hy.trans (map_zero invS).symm)
  have hy' : ιE (Hg p S L φ y) = 0 := congrArg Subtype.val hy0
  obtain ⟨x, hx⟩ := (hιker _).1 hy'
  refine ⟨Submodule.Quotient.mk x, ?_⟩
  rw [ιmap_mk, hx, Hf_Hg]

lemma mem_range_invmap_iff (hιrange : ∀ w : H2E S L, (∃ v, ιE v = w) ↔ p • w = 0) (f) :
    f ∈ LinearMap.range (invmap p S L ιE φ invS hιrange) ↔ f ∈ LinearMap.range invS := by
  constructor
  · rintro ⟨y, rfl⟩; exact ⟨_, rfl⟩
  · rintro ⟨w, rfl⟩
    have hw : p • (w : H2E S L) = 0 := by
      have := (Submodule.mem_torsionBy_iff _ _).1 w.2
      change (p : ℤ) • (w : H2E S L) = 0 at this
      rwa [natCast_zsmul] at this
    obtain ⟨v, hv⟩ := (hιrange _).2 hw
    refine ⟨Hf p S L φ v, ?_⟩
    have hκ : κmap p S L ιE φ hιrange (Hf p S L φ v) = w :=
      Subtype.ext ((κmap_apply_coe p S L ιE φ hιrange _).trans ((congrArg ιE (Hg_Hf p S L φ v)).trans hv))
    exact (invmap_apply p S L ιE φ invS hιrange _).trans (congrArg invS hκ)

end Core
end P2mS25EqBrauerLEq
end

noncomputable section
namespace P2mS25EqBrauerLEq
open NumberField.LevelArith

local notation "Γ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
local notation "Qbar" => (AlgebraicClosure ℚ)

variable {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (L : IntermediateField ℚ (AlgebraicClosure ℚ))
variable (p)

lemma val_smul_torsion (c : ZMod p) (e : T p S L) :
    sUnitsMaxRep.val S L ((c • e : T p S L) : E S L) = (sUnitsMaxRep.val S L (e : E S L)) ^ c.val := by
  conv_lhs => rw [← ZMod.natCast_zmod_val c, Nat.cast_smul_eq_nsmul]
  rfl

lemma val_cycloChar_smul (σ : Γ) (e : T p S L) :
    sUnitsMaxRep.val S L (((cycloChar p σ : (ZMod p)ˣ) : ZMod p) • e : T p S L) = σ • sUnitsMaxRep.val S L (e : E S L) := by
  rw [val_smul_torsion, smul_val_eq_pow_cycloChar (p := p) S L σ]
  exact (Submodule.mem_torsionBy_iff (p : ℤ) (e : E S L)).1 e.2

variable (ιE : H2T p S L →+ H2E S L) (φ : T p S L ≅ Bμ p L)
  (invS : ↥(Submodule.torsionBy ℤ (H2E S L) (p : ℤ)) →ₗ[ZMod p] (↥(placesOverPrimes ↥L (S : Set Nat.Primes)) → ZMod p))

abbrev toT (w : ↥(levelCocyclesSr₂ (rL L) S (Bμ p L))) : ↥(levelCocyclesSr₂ (rL L) S (T p S L)) :=
  levelCocyclesSr₂Map (MonoidHom.id _) (fun _ => rfl) S φ.inv.hom.toLinearMap (fun g a => Rep.hom_comm_apply φ.inv g a) w

lemma toT_apply (w : ↥(levelCocyclesSr₂ (rL L) S (Bμ p L))) (x : ↥L.fixingSubgroup × ↥L.fixingSubgroup) :
    (toT p S L φ w : ↥L.fixingSubgroup × ↥L.fixingSubgroup → T p S L) x = φ.inv.hom ((w : _ → Bμ p L) x) := rfl

lemma Hg_π (w : ↥(levelCocyclesSr₂ (rL L) S (Bμ p L))) :
    Hg p S L φ (continuousH2Srπ (rL L) S (Bμ p L) w) = continuousH2Srπ (rL L) S _ (toT p S L φ w) := rfl

lemma invmap_natural [FiniteDimensional ℚ ↥L] (hιrange : ∀ w : H2E S L, (∃ v, ιE v = w) ↔ p • w = 0)
    (hιpin : ∀ z : ↥(levelCocyclesSr₂ (rL L) S (T p S L)),
      ∃ hz : (fun x => ((z : _ → T p S L) x).1) ∈ levelCocyclesSr₂ (rL L) S (E S L),
        ιE (continuousH2Srπ (rL L) S (T p S L) z) = continuousH2Srπ (rL L) S (E S L) ⟨_, hz⟩)
    (hnatS : ∀ (σ : Γ) (τ : ↥L ≃ₐ[ℚ] ↥L), (∀ y : ↥L, σ (y : Qbar) = ((τ y : ↥L) : Qbar)) →
        ∀ (a a' : ↥(Submodule.torsionBy ℤ (H2E S L) (p : ℤ))) (w w' : ↥(levelCocyclesSr₂ (rL L) S (E S L))),
          (a : H2E S L) = continuousH2Srπ (rL L) S (E S L) w → (a' : H2E S L) = continuousH2Srπ (rL L) S (E S L) w' →
          (∀ s t s' t' : ↥L.fixingSubgroup, σ⁻¹ * (s : Γ) * σ = s' → σ⁻¹ * (t : Γ) * σ = t' →
            sUnitsMaxRep.val S L ((w' : _ → E S L) (s, t)) = σ • sUnitsMaxRep.val S L ((w : _ → E S L) (s', t'))) →
          ∀ (v v' : ↥(placesOverPrimes ↥L (S : Set Nat.Primes))), (∀ y : ↥L, (v'.1).valuation ↥L (τ y) = (v.1).valuation ↥L y) →
            invS a' v' = invS a v)
    (σ : Γ) (τ : ↥L ≃ₐ[ℚ] ↥L) (hστ : ∀ y : ↥L, σ (y : Qbar) = ((τ y : ↥L) : Qbar))
    (w w' : ↥(levelCocyclesSr₂ (rL L) S (Bμ p L)))
    (hrel : ∀ s t s' t' : ↥L.fixingSubgroup, σ⁻¹ * (s : Γ) * σ = s' → σ⁻¹ * (t : Γ) * σ = t' →
      (w' : _ → ZMod p) (s, t) = ((cycloChar p σ : (ZMod p)ˣ) : ZMod p) * (w : _ → ZMod p) (s', t'))
    (v v' : ↥(placesOverPrimes ↥L (S : Set Nat.Primes))) (hvv' : ∀ y : ↥L, (v'.1).valuation ↥L (τ y) = (v.1).valuation ↥L y) :
    invmap p S L ιE φ invS hιrange (continuousH2Srπ (rL L) S (Bμ p L) w') v' = invmap p S L ιE φ invS hιrange (continuousH2Srπ (rL L) S (Bμ p L) w) v := by
  obtain ⟨hz, hzπ⟩ := hιpin (toT p S L φ w)
  obtain ⟨hz', hzπ'⟩ := hιpin (toT p S L φ w')
  have e1 := congrFun (invmap_apply p S L ιE φ invS hιrange (continuousH2Srπ (rL L) S (Bμ p L) w')) v'
  have e2 := congrFun (invmap_apply p S L ιE φ invS hιrange (continuousH2Srπ (rL L) S (Bμ p L) w)) v
  have h1 : ((κmap p S L ιE φ hιrange (continuousH2Srπ (rL L) S (Bμ p L) w) : ↥(Submodule.torsionBy ℤ (H2E S L) (p : ℤ))) : H2E S L) =
      continuousH2Srπ (rL L) S (E S L) ⟨_, hz⟩ := (κmap_apply_coe p S L ιE φ hιrange _).trans hzπ
  have h2 : ((κmap p S L ιE φ hιrange (continuousH2Srπ (rL L) S (Bμ p L) w') : ↥(Submodule.torsionBy ℤ (H2E S L) (p : ℤ))) : H2E S L) =
      continuousH2Srπ (rL L) S (E S L) ⟨_, hz'⟩ := (κmap_apply_coe p S L ιE φ hιrange _).trans hzπ'
  have h3 : ∀ s t s' t' : ↥L.fixingSubgroup, σ⁻¹ * (s : Γ) * σ = s' → σ⁻¹ * (t : Γ) * σ = t' →
      sUnitsMaxRep.val S L (((φ.inv.hom ((w' : _ → Bμ p L) (s, t)) : T p S L) : E S L)) =
        σ • sUnitsMaxRep.val S L (((φ.inv.hom ((w : _ → Bμ p L) (s', t')) : T p S L) : E S L)) := by
    intro s t s' t' hs ht
    have hw : φ.inv.hom ((w' : _ → Bμ p L) (s, t)) = ((cycloChar p σ : (ZMod p)ˣ) : ZMod p) • φ.inv.hom ((w : _ → Bμ p L) (s', t')) := by
      rw [hrel s t s' t' hs ht, ← smul_eq_mul, map_smul]
    rw [hw]
    exact val_cycloChar_smul p S L σ _
  exact e1.trans ((hnatS σ τ hστ _ _ ⟨_, hz⟩ ⟨_, hz'⟩ h1 h2 h3 v v' hvv').trans e2.symm)

end P2mS25EqBrauerLEq
end

noncomputable section
namespace P2mS25EqBrauerLEq
open NumberField.LevelArith

local notation "Γ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
local notation "Qbar" => (AlgebraicClosure ℚ)

variable {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (L : IntermediateField ℚ (AlgebraicClosure ℚ))

lemma val_injective : Function.Injective (sUnitsMaxRep.val S L) := fun x y h =>
  Subtype.ext (Additive.toMul.injective h)

lemma smul_mem_stable (hst : ∀ L' : IntermediateField ℚ Qbar, sUnitsMaxStable S L' = sUnitsMax S) (σ : Γ)
    {x : Qbarˣ} (hx : x ∈ sUnitsMaxStable S L) : σ • x ∈ sUnitsMaxStable S L := by
  rw [hst L] at hx ⊢
  rw [← hst ⊥] at hx ⊢
  have hσ : σ ∈ (⊥ : IntermediateField ℚ Qbar).fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    obtain ⟨r, rfl⟩ := IntermediateField.mem_bot.1 hy
    exact σ.commutes r
  exact smul_mem_sUnitsMaxStable S ⊥ ⟨σ, hσ⟩ hx

def σE (hst : ∀ L' : IntermediateField ℚ Qbar, sUnitsMaxStable S L' = sUnitsMax S) (σ : Γ) : E S L →+ E S L where
  toFun x := ⟨Additive.ofMul (σ • sUnitsMaxRep.val S L x), smul_mem_stable S L hst σ x.2⟩
  map_zero' := by
    apply val_injective S L
    change σ • sUnitsMaxRep.val S L (0 : E S L) = sUnitsMaxRep.val S L (0 : E S L)
    change σ • (1 : Qbarˣ) = 1
    exact smul_one σ
  map_add' x y := by
    apply val_injective S L
    change σ • (sUnitsMaxRep.val S L x * sUnitsMaxRep.val S L y) = σ • sUnitsMaxRep.val S L x * σ • sUnitsMaxRep.val S L y
    exact smul_mul' σ _ _

lemma val_σE (hst : ∀ L' : IntermediateField ℚ Qbar, sUnitsMaxStable S L' = sUnitsMax S) (σ : Γ) (x : E S L) :
    sUnitsMaxRep.val S L (σE S L hst σ x) = σ • sUnitsMaxRep.val S L x := rfl

lemma σE_ρ (hst : ∀ L' : IntermediateField ℚ Qbar, sUnitsMaxStable S L' = sUnitsMax S) (σ : Γ) (s s' : ↥L.fixingSubgroup)
    (hs : σ⁻¹ * (s : Γ) * σ = s') (x : E S L) : σE S L hst σ ((E S L).ρ s' x) = (E S L).ρ s (σE S L hst σ x) := by
  apply val_injective S L
  rw [val_σE, sUnitsMaxRep.val_ρ, sUnitsMaxRep.val_ρ, val_σE, ← mul_smul, ← mul_smul, ← hs]
  congr 1
  group

variable (p) in

lemma σE_torsion (hst : ∀ L' : IntermediateField ℚ Qbar, sUnitsMaxStable S L' = sUnitsMax S) (σ : Γ) (e : T p S L) :
    σE S L hst σ (e : E S L) = ((((cycloChar p σ : (ZMod p)ˣ) : ZMod p) • e : T p S L) : E S L) := by
  apply val_injective S L
  rw [val_σE, val_cycloChar_smul]

def cj (σ : Γ) (τ : ↥L ≃ₐ[ℚ] ↥L) (hστ : ∀ y : ↥L, σ (y : Qbar) = ((τ y : ↥L) : Qbar)) : ↥L.fixingSubgroup →* ↥L.fixingSubgroup where
  toFun s := ⟨σ⁻¹ * (s : Γ) * σ, by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    have h1 : σ y = ((τ ⟨y, hy⟩ : ↥L) : Qbar) := hστ ⟨y, hy⟩
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, h1, (IntermediateField.mem_fixingSubgroup_iff _ _).1 s.2 _ (τ ⟨y, hy⟩).2, ← h1]
    exact σ.symm_apply_apply y⟩
  map_one' := Subtype.ext (by simp)
  map_mul' s t := Subtype.ext (by change σ⁻¹ * ((s : Γ) * t) * σ = σ⁻¹ * s * σ * (σ⁻¹ * t * σ); group)

lemma coe_cj (σ : Γ) (τ : ↥L ≃ₐ[ℚ] ↥L) (hστ) (s : ↥L.fixingSubgroup) : ((cj L σ τ hστ s : ↥L.fixingSubgroup) : Γ) = σ⁻¹ * (s : Γ) * σ := rfl

lemma cj_eq (σ : Γ) (τ : ↥L ≃ₐ[ℚ] ↥L) (hστ) {s s' : ↥L.fixingSubgroup} (h : σ⁻¹ * (s : Γ) * σ = s') : cj L σ τ hστ s = s' :=
  Subtype.ext h

end P2mS25EqBrauerLEq
end

noncomputable section
namespace P2mS25EqBrauerLEq
open NumberField.LevelArith

local instance isAlgebraicQbar : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
local instance isAlgClosureQbar : IsAlgClosure ℚ (AlgebraicClosure ℚ) := ⟨inferInstance, inferInstance⟩
local instance normalQbar : Normal ℚ (AlgebraicClosure ℚ) := IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)

local notation "Γ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
local notation "Qbar" => (AlgebraicClosure ℚ)

lemma conj_mem_fixingSubgroup' (K : IntermediateField ℚ Qbar) [Normal ℚ K] {s : Γ} (hs : s ∈ K.fixingSubgroup) (x : Γ) :
    x * s * x⁻¹ ∈ K.fixingSubgroup := by
  rw [IntermediateField.mem_fixingSubgroup_iff] at hs ⊢
  intro y hy
  have hle := IntermediateField.normal_iff_forall_map_le'.mp (inferInstance : Normal ℚ K) x⁻¹
  have hy' : x⁻¹ y ∈ K := hle ⟨y, hy, rfl⟩
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hs _ hy']
  simp

lemma exists_normal_level' {S : Finset Nat.Primes} {F : IntermediateField ℚ Qbar} (hF : F.IsUnramifiedOutside S) :
    ∃ N : IntermediateField ℚ Qbar, N.IsUnramifiedOutside S ∧ N.fixingSubgroup ≤ F.fixingSubgroup ∧
      ∀ (s : Γ), s ∈ N.fixingSubgroup → ∀ x : Γ, x⁻¹ * s * x ∈ N.fixingSubgroup := by
  haveI : FiniteDimensional ℚ ↥F := hF.1
  refine ⟨IntermediateField.normalClosure ℚ (↥F) Qbar, IntermediateField.IsUnramifiedOutside.normalClosure hF,
    IntermediateField.fixingSubgroup_antitone (IntermediateField.le_normalClosure F), fun s hs x => ?_⟩
  haveI : Normal ℚ ↥(IntermediateField.normalClosure ℚ (↥F) Qbar) := normalClosure.normal ℚ (↥F) Qbar
  have := conj_mem_fixingSubgroup' (IntermediateField.normalClosure ℚ (↥F) Qbar) hs x⁻¹
  rwa [inv_inv] at this

variable {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (L : IntermediateField ℚ (AlgebraicClosure ℚ))
variable (p)

variable (δ : H1E S L →+ H2T p S L) (φ : T p S L ≅ Bμ p L)

abbrev toB (z : ↥(levelCocyclesSr₂ (rL L) S (T p S L))) : ↥(levelCocyclesSr₂ (rL L) S (Bμ p L)) :=
  levelCocyclesSr₂Map (MonoidHom.id _) (fun _ => rfl) S φ.hom.hom.toLinearMap (fun g a => Rep.hom_comm_apply φ.hom g a) z

lemma Hf_π (z : ↥(levelCocyclesSr₂ (rL L) S (T p S L))) :
    Hf p S L φ (continuousH2Srπ (rL L) S (T p S L) z) = continuousH2Srπ (rL L) S (Bμ p L) (toB p S L φ z) := rfl

set_option maxHeartbeats 6400000 in

lemma ιmap_natural (hst : ∀ L' : IntermediateField ℚ Qbar, sUnitsMaxStable S L' = sUnitsMax S)
    (hdiv : ∀ x : E S L, ∃ y : E S L, (p : ℤ) • y = x)
    (hδpin : ∀ (c : ↥(levelCocyclesSr₁ (rL L) S (E S L))) (b : ↥L.fixingSubgroup → E S L), IsLevelConstantSr₁ (rL L) S b →
        (∀ g, p • b g = (c.1 : ↥L.fixingSubgroup → E S L) g) →
        ∃ w : ↥(levelCocyclesSr₂ (rL L) S (T p S L)),
          (∀ x : ↥L.fixingSubgroup × ↥L.fixingSubgroup, ((w : _ → T p S L) x).1 = (d₁₂ (E S L)).hom b x) ∧
          δ ⟨(H1π (E S L)).hom c.1, H1π_mem_continuousH1Sr (rL L) S (E S L) c.2⟩ = continuousH2Srπ (rL L) S (T p S L) w)
    (σ : Γ) (τ : ↥L ≃ₐ[ℚ] ↥L) (hστ : ∀ y : ↥L, σ (y : Qbar) = ((τ y : ↥L) : Qbar))
    (c c' : ↥(levelCocyclesSr₁ (rL L) S (E S L)))
    (hcc' : ∀ s s' : ↥L.fixingSubgroup, σ⁻¹ * (s : Γ) * σ = s' →
      sUnitsMaxRep.val S L ((c'.1 : ↥L.fixingSubgroup → E S L) s) = σ • sUnitsMaxRep.val S L ((c.1 : ↥L.fixingSubgroup → E S L) s')) :
    ∃ w w' : ↥(levelCocyclesSr₂ (rL L) S (Bμ p L)),
      ιmap p S L δ φ (Submodule.Quotient.mk ⟨(H1π (E S L)).hom c.1, H1π_mem_continuousH1Sr (rL L) S (E S L) c.2⟩) =
        continuousH2Srπ (rL L) S (Bμ p L) w ∧
      ιmap p S L δ φ (Submodule.Quotient.mk ⟨(H1π (E S L)).hom c'.1, H1π_mem_continuousH1Sr (rL L) S (E S L) c'.2⟩) =
        continuousH2Srπ (rL L) S (Bμ p L) w' ∧
      ∀ s t s' t' : ↥L.fixingSubgroup, σ⁻¹ * (s : Γ) * σ = s' → σ⁻¹ * (t : Γ) * σ = t' →
        (w' : _ → ZMod p) (s, t) = ((cycloChar p σ : (ZMod p)ˣ) : ZMod p) * (w : _ → ZMod p) (s', t') := by

  obtain ⟨root, hroot⟩ : ∃ root : E S L → E S L, ∀ x, (p : ℤ) • root x = x :=
    ⟨fun x => Classical.choose (hdiv x), fun x => Classical.choose_spec (hdiv x)⟩
  obtain ⟨b, hbdef⟩ : ∃ b : ↥L.fixingSubgroup → E S L, ∀ g, b g = root ((c.1 : ↥L.fixingSubgroup → E S L) g) :=
    ⟨_, fun _ => rfl⟩
  have hb : ∀ g, p • b g = (c.1 : ↥L.fixingSubgroup → E S L) g := fun g => by rw [hbdef, ← natCast_zsmul]; exact hroot _
  obtain ⟨F, hF, hcF⟩ := (mem_levelCocyclesSr₁_iff (rL L) S (E S L) c.1).1 c.2
  have hb_lc : IsLevelConstantSr₁ (rL L) S b := ⟨F, hF, fun g s hs => by rw [hbdef, hbdef, hcF g s hs]⟩
  obtain ⟨W, hW, hδW⟩ := hδpin c b hb_lc hb

  obtain ⟨N, hN, hNF, hconj⟩ := exists_normal_level' hF
  obtain ⟨b', hb'def⟩ : ∃ b' : ↥L.fixingSubgroup → E S L, ∀ s, b' s = σE S L hst σ (b (cj L σ τ hστ s)) := ⟨_, fun _ => rfl⟩
  have hb' : ∀ s, p • b' s = (c'.1 : ↥L.fixingSubgroup → E S L) s := fun s => by
    rw [hb'def, ← map_nsmul (σE S L hst σ) p, hb]
    apply val_injective S L
    exact (val_σE S L hst σ _).trans (hcc' s (cj L σ τ hστ s) rfl).symm
  have hb'_lc : IsLevelConstantSr₁ (rL L) S b' := ⟨N, hN, fun g u hu => by
    rw [hb'def, hb'def, (cj L σ τ hστ).map_mul g u, hbdef, hbdef, hcF _ _ (hNF (hconj _ hu σ))]⟩
  obtain ⟨W', hW', hδW'⟩ := hδpin c' b' hb'_lc hb'
  refine ⟨toB p S L φ W, toB p S L φ W', ?_, ?_, ?_⟩
  · exact (ιmap_mk p S L δ φ _).trans (congrArg (Hf p S L φ) hδW)
  · exact (ιmap_mk p S L δ φ _).trans (congrArg (Hf p S L φ) hδW')
  · intro s t s' t' hs ht
    change φ.hom.hom ((W' : _ → T p S L) (s, t)) = ((cycloChar p σ : (ZMod p)ˣ) : ZMod p) * φ.hom.hom ((W : _ → T p S L) (s', t'))
    have key : (W' : _ → T p S L) (s, t) = ((cycloChar p σ : (ZMod p)ˣ) : ZMod p) • (W : _ → T p S L) (s', t') := by
      apply Subtype.ext
      rw [hW' (s, t), ← σE_torsion p S L hst σ, hW (s', t'), d₁₂_hom_apply, d₁₂_hom_apply, (σE S L hst σ).map_add,
        (σE S L hst σ).map_sub]
      dsimp only
      rw [hb'def, hb'def, hb'def, (cj L σ τ hστ).map_mul s t, cj_eq L σ τ hστ hs, cj_eq L σ τ hστ ht, σE_ρ S L hst σ s s' hs]
    rw [key, map_smul, smul_eq_mul]

end P2mS25EqBrauerLEq
end

noncomputable section
namespace P2mS25EqBrauerLEq
open NumberField.LevelArith

set_option maxHeartbeats 16000000 in

theorem core
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hL : L.IsUnramifiedOutside S) [FiniteDimensional ℚ ↥L]
    (h4 : p = 2 → ∃ i ∈ L, i ^ 2 = -1) :
    ∃ (ι : ((H1E S L) ⧸ ((p : ℤ) • (⊤ : Submodule ℤ (H1E S L)))) →ₗ[ZMod p] (H2B p S L)) (inv : (H2B p S L) →ₗ[ZMod p] (↥(placesOverPrimes ↥L (S : Set Nat.Primes)) → ZMod p)),
      Function.Injective ι ∧ LinearMap.range ι = LinearMap.ker inv ∧ (∀ f, f ∈ LinearMap.range inv ↔ ∑ᶠ w, f w = 0) ∧
      ∀ (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (τ : ↥L ≃ₐ[ℚ] ↥L), (∀ y : ↥L, σ (y : AlgebraicClosure ℚ) = ((τ y : ↥L) : AlgebraicClosure ℚ)) →

        (∀ (w w' : ↥(levelCocyclesSr₂ (rL L) S (Bμ p L))),
          (∀ s t s' t' : ↥L.fixingSubgroup, σ⁻¹ * (s : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) * σ = s' → σ⁻¹ * (t : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) * σ = t' →
            (w' : ↥L.fixingSubgroup × ↥L.fixingSubgroup → ZMod p) (s, t) =
              ((cycloChar p σ : (ZMod p)ˣ) : ZMod p) * (w : ↥L.fixingSubgroup × ↥L.fixingSubgroup → ZMod p) (s', t')) →
          ∀ (v v' : ↥(placesOverPrimes ↥L (S : Set Nat.Primes))), (∀ y : ↥L, (v'.1).valuation ↥L (τ y) = (v.1).valuation ↥L y) →
            inv (continuousH2Srπ (rL L) S (Bμ p L) w') v' = inv (continuousH2Srπ (rL L) S (Bμ p L) w) v) ∧

        (∀ (c c' : ↥(levelCocyclesSr₁ (rL L) S (E S L))),
          (∀ s s' : ↥L.fixingSubgroup, σ⁻¹ * (s : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) * σ = s' →
            sUnitsMaxRep.val S L ((c'.1 : ↥L.fixingSubgroup → (E S L)) s) = σ • sUnitsMaxRep.val S L ((c.1 : ↥L.fixingSubgroup → (E S L)) s')) →
          ∃ w w' : ↥(levelCocyclesSr₂ (rL L) S (Bμ p L)),
            ι (Submodule.Quotient.mk ⟨(H1π (E S L)).hom c.1, H1π_mem_continuousH1Sr (rL L) S (E S L) c.2⟩) =
              continuousH2Srπ (rL L) S (Bμ p L) w ∧
            ι (Submodule.Quotient.mk ⟨(H1π (E S L)).hom c'.1, H1π_mem_continuousH1Sr (rL L) S (E S L) c'.2⟩) =
              continuousH2Srπ (rL L) S (Bμ p L) w' ∧
            ∀ s t s' t' : ↥L.fixingSubgroup, σ⁻¹ * (s : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) * σ = s' → σ⁻¹ * (t : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) * σ = t' →
              (w' : ↥L.fixingSubgroup × ↥L.fixingSubgroup → ZMod p) (s, t) =
                ((cycloChar p σ : (ZMod p)ˣ) : ZMod p) * (w : ↥L.fixingSubgroup × ↥L.fixingSubgroup → ZMod p) (s', t')) := by
  obtain ⟨hsm, hdiv⟩ := NumberField.LevelArith.sUnitsMaxRep_smooth_and_divisible S hpS L (p := p)
  obtain ⟨δ, ιE, hδker, hιker, hιrange, hιpin, hδpin⟩ :=
    groupCohomology.exists_kummer_connecting_maps_continuousHSr_of_smooth_of_divisible (p := p) S L.fixingSubgroup.subtype
      (sUnitsMaxRep S L) hsm hdiv
  obtain ⟨φ⟩ := NumberField.LevelArith.nonempty_repTorsionP_sUnitsMaxRep_iso_trivial_twist_cycloChar S hpS L (p := p)
  obtain ⟨invS, hinvS, hrangeS, hnatS⟩ := groupCohomology.exists_natural_localInv_torsionBy_continuousH2Sr_sUnitsMax S hpS L hL h4 (p := p)
  have hst : ∀ L' : IntermediateField ℚ (AlgebraicClosure ℚ), sUnitsMaxStable S L' = sUnitsMax S :=
    fun L' => NumberField.LevelArith.sUnitsMaxStable_eq_sUnitsMax S L'
  refine ⟨ιmap p S L δ φ, invmap p S L ιE φ invS hιrange, ιmap_injective p S L δ φ hδker,
    le_antisymm (range_ιmap_le_ker p S L δ ιE φ invS hιker hιrange) (ker_le_range_ιmap p S L δ ιE φ invS hιker hιrange hinvS),
    fun f => (mem_range_invmap_iff p S L ιE φ invS hιrange f).trans (hrangeS f), fun σ τ hστ => ⟨?_, ?_⟩⟩
  · intro w w' hrel v v' hvv'
    exact invmap_natural p S L ιE φ invS hιrange hιpin hnatS σ τ hστ w w' hrel v v' hvv'
  · intro c c' hcc'
    exact ιmap_natural p S L δ φ hst hdiv hδpin σ τ hστ c c' hcc'

end P2mS25EqBrauerLEq
end

open P2mS25EqBrauerLEq in
theorem solution
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hL : L.IsUnramifiedOutside S) [FiniteDimensional ℚ ↥L]
    (h4 : p = 2 → ∃ i ∈ L, i ^ 2 = -1) :
    ∃ (ι : (↥(continuousH1Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L)) ⧸ ((p : ℤ) • (⊤ : Submodule ℤ ↥(continuousH1Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L))))) →ₗ[ZMod p] (continuousH2Sr L.fixingSubgroup.subtype S ((Rep.trivial (ZMod p) ↥L.fixingSubgroup (ZMod p)).twist ((cycloChar p).comp L.fixingSubgroup.subtype)))) (inv : (continuousH2Sr L.fixingSubgroup.subtype S ((Rep.trivial (ZMod p) ↥L.fixingSubgroup (ZMod p)).twist ((cycloChar p).comp L.fixingSubgroup.subtype))) →ₗ[ZMod p] (↥(placesOverPrimes ↥L (S : Set Nat.Primes)) → ZMod p)),
      Function.Injective ι ∧ LinearMap.range ι = LinearMap.ker inv ∧ (∀ f, f ∈ LinearMap.range inv ↔ ∑ᶠ w, f w = 0) ∧
      ∀ (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (τ : ↥L ≃ₐ[ℚ] ↥L), (∀ y : ↥L, σ (y : AlgebraicClosure ℚ) = ((τ y : ↥L) : AlgebraicClosure ℚ)) →

        (∀ (w w' : ↥(levelCocyclesSr₂ L.fixingSubgroup.subtype S ((Rep.trivial (ZMod p) ↥L.fixingSubgroup (ZMod p)).twist ((cycloChar p).comp L.fixingSubgroup.subtype)))),
          (∀ s t s' t' : ↥L.fixingSubgroup, σ⁻¹ * (s : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) * σ = s' → σ⁻¹ * (t : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) * σ = t' →
            (w' : ↥L.fixingSubgroup × ↥L.fixingSubgroup → ZMod p) (s, t) =
              ((cycloChar p σ : (ZMod p)ˣ) : ZMod p) * (w : ↥L.fixingSubgroup × ↥L.fixingSubgroup → ZMod p) (s', t')) →
          ∀ (v v' : ↥(placesOverPrimes ↥L (S : Set Nat.Primes))), (∀ y : ↥L, (v'.1).valuation ↥L (τ y) = (v.1).valuation ↥L y) →
            inv (continuousH2Srπ L.fixingSubgroup.subtype S _ w') v' = inv (continuousH2Srπ L.fixingSubgroup.subtype S _ w) v) ∧

        (∀ (c c' : ↥(levelCocyclesSr₁ L.fixingSubgroup.subtype S (sUnitsMaxRep S L))),
          (∀ s s' : ↥L.fixingSubgroup, σ⁻¹ * (s : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) * σ = s' →
            sUnitsMaxRep.val S L ((c'.1 : ↥L.fixingSubgroup → (sUnitsMaxRep S L)) s) = σ • sUnitsMaxRep.val S L ((c.1 : ↥L.fixingSubgroup → (sUnitsMaxRep S L)) s')) →
          ∃ w w' : ↥(levelCocyclesSr₂ L.fixingSubgroup.subtype S ((Rep.trivial (ZMod p) ↥L.fixingSubgroup (ZMod p)).twist ((cycloChar p).comp L.fixingSubgroup.subtype))),
            ι (Submodule.Quotient.mk ⟨(H1π (sUnitsMaxRep S L)).hom c.1, H1π_mem_continuousH1Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L) c.2⟩) =
              continuousH2Srπ L.fixingSubgroup.subtype S _ w ∧
            ι (Submodule.Quotient.mk ⟨(H1π (sUnitsMaxRep S L)).hom c'.1, H1π_mem_continuousH1Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L) c'.2⟩) =
              continuousH2Srπ L.fixingSubgroup.subtype S _ w' ∧
            ∀ s t s' t' : ↥L.fixingSubgroup, σ⁻¹ * (s : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) * σ = s' → σ⁻¹ * (t : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) * σ = t' →
              (w' : ↥L.fixingSubgroup × ↥L.fixingSubgroup → ZMod p) (s, t) =
                ((cycloChar p σ : (ZMod p)ˣ) : ZMod p) * (w : ↥L.fixingSubgroup × ↥L.fixingSubgroup → ZMod p) (s', t')) :=
  core S hpS L hL h4

end S_groupCohomology_exists_kummerBrauer_maps_continuousH2Sr_cyclotomic_natural
end P2MW
export P2MW.S_groupCohomology_exists_kummerBrauer_maps_continuousH2Sr_cyclotomic_natural (solution)
