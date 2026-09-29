-- Prove2me | solution 1 for groupCohomology.bijective_theta_dualTwist_of_primeLocal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/b7d62f5f-b81d-5a35-aeb3-3c8e37f2eb21

import Mathlib
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_ContinuousH2Map
import Definitions.Def_GroupCohomology_ContinuousH1
import Definitions.Def_GroupCohomology_CupProduct
import Definitions.Def_GroupCohomology_ContinuousDuality
import Definitions.Def_GroupCohomology_Selmer
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Theorems.Thm_groupCohomology_exists_level_sylow_of_primeLocal
import Theorems.Thm_groupCohomology_bijective_theta_dualTwist_of_sylowLevel
import Theorems.Thm_groupCohomology_bijective_theta_dualTwist_of_res
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_bijective_theta_dualTwist_of_primeLocal
p2m_attr_erase "instance" "ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal groupCohomology.normal_comap_fixingSubgroup groupCohomology.finiteIndex_comap_fixingSubgroup ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete groupCohomology.Kummer.instMulDistribMulActionRootsOfUnity"
p2m_attr_erase "simp" "ExtCitation.LocalLevel.coe_smul_OO WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply groupCohomology.Kummer.coe_kummerCocycleRoots groupCohomology.Kummer.mem_powerSubgroup_iff groupCohomology.Kummer.val_smul_units groupCohomology.Kummer.kummerHom_apply groupCohomology.Kummer.coe_smul_rootsOfUnity groupCohomology.unitsInflate₁_apply groupCohomology.unitsInflate₂_apply IsLocalRing.principalUnits_zero"

set_option autoImplicit false
open CategoryTheory Module groupCohomology ExtCitation

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    {p : ℕ} [Fact p.Prime] (q : Nat.Primes)
    (M : Rep (ZMod p) (primeLocalGaloisGroup q)) [FiniteDimensional (ZMod p) M]
    (hsm : ∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s, primeLocalToGlobal q s ∈ F.fixingSubgroup → M.ρ s m = m)
    (inv : continuousH2 (primeLocalToGlobal q) (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))) →ₗ[ZMod p] ZMod p)
    (hinv : Function.Bijective inv)
    (θ₀ : M.ρ.invariants →ₗ[ZMod p] Module.Dual (ZMod p)
      (continuousH2 (primeLocalToGlobal q) (M.dualTwist ((cycloChar p).comp (primeLocalToGlobal q)))))
    (hθ₀ : IsTheta0 (primeLocalToGlobal q)
      (Module.Dual.eval (ZMod p) M : M →ₗ[ZMod p] M.dualTwist ((cycloChar p).comp (primeLocalToGlobal q)) →ₗ[ZMod p]
        ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))) inv θ₀)
    (θ₁ : continuousH1 (primeLocalToGlobal q) M →ₗ[ZMod p] Module.Dual (ZMod p)
      (continuousH1 (primeLocalToGlobal q) (M.dualTwist ((cycloChar p).comp (primeLocalToGlobal q)))))
    (hθ₁ : IsTheta1 (primeLocalToGlobal q)
      (Module.Dual.eval (ZMod p) M : M →ₗ[ZMod p] M.dualTwist ((cycloChar p).comp (primeLocalToGlobal q)) →ₗ[ZMod p]
        ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))) inv θ₁)
    (θ₂ : continuousH2 (primeLocalToGlobal q) M →ₗ[ZMod p] Module.Dual (ZMod p)
      (M.dualTwist ((cycloChar p).comp (primeLocalToGlobal q))).ρ.invariants)
    (hθ₂ : IsTheta2 (primeLocalToGlobal q)
      (Module.Dual.eval (ZMod p) M : M →ₗ[ZMod p] M.dualTwist ((cycloChar p).comp (primeLocalToGlobal q)) →ₗ[ZMod p]
        ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))) inv θ₂) :
    Function.Bijective θ₀ ∧ Function.Bijective θ₁ ∧ Function.Bijective θ₂ := by
  obtain ⟨U, S, hUS, hUn, hUo, hSf, hSp, hSU, hUM, hχU⟩ := groupCohomology.exists_level_sylow_of_primeLocal q M hsm
  haveI := hUn; haveI := hSf
  have hSo : ∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧
      F₀.fixingSubgroup.comap (primeLocalToGlobal q) ≤ S := by
    obtain ⟨F₀, hF₀, h⟩ := hUo
    exact ⟨F₀, hF₀, h.trans hUS⟩
  refine groupCohomology.bijective_theta_dualTwist_of_res q S hSp hSo M hsm inv hinv ?_ θ₀ hθ₀ θ₁ hθ₁ θ₂ hθ₂
  intro invS hinvS φ₀ hφ₀ φ₁ hφ₁ φ₂ hφ₂
  exact groupCohomology.bijective_theta_dualTwist_of_sylowLevel q S hSo U hSU hχU (Rep.res S.subtype M)
    (fun a => by
      obtain ⟨F, hF, h⟩ := hsm a
      exact ⟨F, hF, fun s hs => h (s : primeLocalGaloisGroup q) hs⟩)
    (fun s hs a => hUM s hs a) invS hinvS φ₀ hφ₀ φ₁ hφ₁ φ₂ hφ₂

end S_groupCohomology_bijective_theta_dualTwist_of_primeLocal
end P2MW
export P2MW.S_groupCohomology_bijective_theta_dualTwist_of_primeLocal (solution)
