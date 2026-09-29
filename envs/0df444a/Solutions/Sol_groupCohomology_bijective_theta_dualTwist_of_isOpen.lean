-- Prove2me | solution 1 for groupCohomology.bijective_theta_dualTwist_of_isOpen
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/f91986fe-60b4-5a94-84a9-c1d8e22de208

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
import Theorems.Thm_groupCohomology_exists_level_sylow_of_isOpen
import Theorems.Thm_groupCohomology_bijective_theta_dualTwist_of_res_of_isOpen
import Theorems.Thm_groupCohomology_bijective_theta_of_mulEquiv
import Theorems.Thm_groupCohomology_nonempty_continuous_linearEquiv_of_mulEquiv
import Theorems.Thm_groupCohomology_finrank_continuousH2_ofChar_cycloChar_of_isOpen
import Theorems.Thm_groupCohomology_bijective_theta_dualTwist_of_sylowLevel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_bijective_theta_dualTwist_of_isOpen
p2m_attr_erase "instance" "groupCohomology.normal_comap_fixingSubgroup groupCohomology.finiteIndex_comap_fixingSubgroup groupCohomology.Kummer.instMulDistribMulActionRootsOfUnity ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal"
p2m_attr_erase "simp" "groupCohomology.Kummer.coe_kummerCocycleRoots groupCohomology.Kummer.mem_powerSubgroup_iff groupCohomology.Kummer.val_smul_units groupCohomology.Kummer.kummerHom_apply groupCohomology.Kummer.coe_smul_rootsOfUnity groupCohomology.unitsInflate₁_apply groupCohomology.unitsInflate₂_apply ExtCitation.LocalLevel.coe_smul_OO WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply IsLocalRing.principalUnits_zero"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
open CategoryTheory Module groupCohomology ExtCitation

set_option maxHeartbeats 6400000 in
theorem solution
    {p : ℕ} [Fact p.Prime] (q : Nat.Primes)
    (S : Subgroup (primeLocalGaloisGroup q))
    (hS : ∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧
      F₀.fixingSubgroup.comap (primeLocalToGlobal q) ≤ S)
    (M : Rep.{0} (ZMod p) S) [FiniteDimensional (ZMod p) M]
    (hsm : ∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s : S, ((primeLocalToGlobal q).comp S.subtype) s ∈ F.fixingSubgroup → M.ρ s m = m)
    (inv : continuousH2 ((primeLocalToGlobal q).comp S.subtype) (Rep.res S.subtype (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))) →ₗ[ZMod p] ZMod p)
    (hinv : Function.Bijective inv)
    (θ₀ : M.ρ.invariants →ₗ[ZMod p] Module.Dual (ZMod p) (continuousH2 ((primeLocalToGlobal q).comp S.subtype) (M.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype))))
    (hθ₀ : IsTheta0 ((primeLocalToGlobal q).comp S.subtype) (Module.Dual.eval (ZMod p) M : M →ₗ[ZMod p] M.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype) →ₗ[ZMod p]
        Rep.res S.subtype (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))) inv θ₀)
    (θ₁ : continuousH1 ((primeLocalToGlobal q).comp S.subtype) M →ₗ[ZMod p] Module.Dual (ZMod p) (continuousH1 ((primeLocalToGlobal q).comp S.subtype) (M.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype))))
    (hθ₁ : IsTheta1 ((primeLocalToGlobal q).comp S.subtype) (Module.Dual.eval (ZMod p) M : M →ₗ[ZMod p] M.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype) →ₗ[ZMod p]
        Rep.res S.subtype (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))) inv θ₁)
    (θ₂ : continuousH2 ((primeLocalToGlobal q).comp S.subtype) M →ₗ[ZMod p] Module.Dual (ZMod p) (M.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype)).ρ.invariants)
    (hθ₂ : IsTheta2 ((primeLocalToGlobal q).comp S.subtype) (Module.Dual.eval (ZMod p) M : M →ₗ[ZMod p] M.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp S.subtype) →ₗ[ZMod p]
        Rep.res S.subtype (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))) inv θ₂) :
    Function.Bijective θ₀ ∧ Function.Bijective θ₁ ∧ Function.Bijective θ₂ := by
  classical
  obtain ⟨U₀, T, hTS, hTopen, hTfi, hTunit, hSU, hUA, hχU⟩ :=
    groupCohomology.exists_level_sylow_of_isOpen q S hS M hsm
  haveI := hTfi

  let e : ↥(T.subgroupOf S) ≃* T := Subgroup.subgroupOfEquivOfLe hTS
  have he : ∀ g : ↥(T.subgroupOf S), ((primeLocalToGlobal q).comp T.subtype) (e.toMonoidHom g)
      = ((((primeLocalToGlobal q).comp S.subtype)).comp (T.subgroupOf S).subtype) g := fun _ => rfl
  have hUopen : ∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧
      F₀.fixingSubgroup.comap ((primeLocalToGlobal q).comp S.subtype) ≤ T.subgroupOf S := by
    obtain ⟨F₀, hF₀, h⟩ := hTopen
    exact ⟨F₀, hF₀, fun s hs => Subgroup.mem_subgroupOf.2 (h hs)⟩

  have hTU : FiniteDimensional (ZMod p) (continuousH2 ((((primeLocalToGlobal q).comp S.subtype)).comp (T.subgroupOf S).subtype)
        (Rep.res (T.subgroupOf S).subtype (Rep.res S.subtype (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))))) ∧
      finrank (ZMod p) (continuousH2 ((((primeLocalToGlobal q).comp S.subtype)).comp (T.subgroupOf S).subtype)
        (Rep.res (T.subgroupOf S).subtype (Rep.res S.subtype (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))))) = 1 := by
    obtain ⟨hfdT, h1T⟩ := groupCohomology.finrank_continuousH2_ofChar_cycloChar_of_isOpen (p := p) q T hTopen
    haveI := hfdT
    obtain ⟨-, -, ⟨E⟩⟩ := groupCohomology.nonempty_continuous_linearEquiv_of_mulEquiv
      (((((primeLocalToGlobal q).comp S.subtype)).comp (T.subgroupOf S).subtype)) ((primeLocalToGlobal q).comp T.subtype) e (fun g => rfl)
      (Rep.res (T.subgroupOf S).subtype (Rep.res S.subtype (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))))
      (Rep.res T.subtype (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))))
      (LinearEquiv.refl (ZMod p) _) (fun _ _ => rfl)
    exact ⟨LinearEquiv.finiteDimensional E.symm, by rw [E.finrank_eq, h1T]⟩

  refine groupCohomology.bijective_theta_dualTwist_of_res_of_isOpen q S (T.subgroupOf S) hTunit hUopen hTU M hsm inv hinv
    ?_ θ₀ hθ₀ θ₁ hθ₁ θ₂ hθ₂
  intro invU hinvU Θ₀ hΘ₀ Θ₁ hΘ₁ Θ₂ hΘ₂

  let MT : Rep (ZMod p) T := Rep.res (Subgroup.inclusion hTS) M
  haveI : FiniteDimensional (ZMod p) MT := ‹FiniteDimensional (ZMod p) M›
  have hsmT : ∀ a : MT, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s : T, ((primeLocalToGlobal q).comp T.subtype) s ∈ F.fixingSubgroup → MT.ρ s a = a := by
    intro a
    obtain ⟨F, hF, h⟩ := hsm a
    exact ⟨F, hF, fun s hs => h (Subgroup.inclusion hTS s) hs⟩
  have hUAT : ∀ s : T, (s : primeLocalGaloisGroup q) ∈ U₀ → ∀ a : MT, MT.ρ s a = a :=
    fun s hs a => hUA (Subgroup.inclusion hTS s) hs a
  exact groupCohomology.bijective_theta_of_mulEquiv ((primeLocalToGlobal q).comp T.subtype)
    ((((primeLocalToGlobal q).comp S.subtype)).comp (T.subgroupOf S).subtype) e he
    (M := MT) (D := MT.dualTwist (((cycloChar p).comp (primeLocalToGlobal q)).comp T.subtype))
    (N := Rep.res T.subtype (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))))
    (Module.Dual.eval (ZMod p) MT) invU hinvU
    (fun hbij ϑ₀ hϑ₀ ϑ₁ hϑ₁ ϑ₂ hϑ₂ =>
      groupCohomology.bijective_theta_dualTwist_of_sylowLevel q T hTopen U₀ hSU hχU MT hsmT hUAT _ hbij
        ϑ₀ hϑ₀ ϑ₁ hϑ₁ ϑ₂ hϑ₂)
    Θ₀ hΘ₀ Θ₁ hΘ₁ Θ₂ hΘ₂

end S_groupCohomology_bijective_theta_dualTwist_of_isOpen
end P2MW
export P2MW.S_groupCohomology_bijective_theta_dualTwist_of_isOpen (solution)
