-- Prove2me | solution 1 for groupCohomology.isLocalInv_localInv_and_bijective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/5e439829-0ce2-594d-8791-2af7c98922a3

import Mathlib
import Definitions.Def_GroupCohomology_LocalInvariant
import Theorems.Thm_groupCohomology_exists_levelCocycles2_ofChar_cycloChar_isLocalInv_witness
import Theorems.Thm_groupCohomology_existsUnique_isLocalInv
import Theorems.Thm_groupCohomology_finrank_continuousH2_ofChar_cycloChar_of_primeLocal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_isLocalInv_localInv_and_bijective
p2m_attr_erase "instance" "groupCohomology.Kummer.instMulDistribMulActionRootsOfUnity ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal"
p2m_attr_erase "simp" "groupCohomology.Kummer.coe_kummerCocycleRoots groupCohomology.Kummer.mem_powerSubgroup_iff groupCohomology.Kummer.val_smul_units groupCohomology.Kummer.kummerHom_apply groupCohomology.Kummer.coe_smul_rootsOfUnity ExtCitation.LocalLevel.coe_smul_OO WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply groupCohomology.cochainsPullPush₁_apply groupCohomology.cochainsPullPush₂_apply groupCohomology.coe_levelCocycles₂Map groupCohomology.continuousH2Map_continuousH2π IsLocalRing.principalUnits_zero"

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000
open CategoryTheory ExtCitation groupCohomology

theorem solution
    (p : ℕ) [Fact p.Prime] (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p) (q : Nat.Primes) [Fact ((q : ℕ)).Prime] :
    IsLocalInv p ζ q (localInv p ζ q) ∧ Function.Bijective (localInv p ζ q) := by
  classical
  have hp : p.Prime := Fact.out
  let Mμ : Rep (ZMod p) (primeLocalGaloisGroup q) := ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))
  let H := continuousH2 (primeLocalToGlobal q) Mμ

  obtain ⟨f, hf, hfu⟩ := groupCohomology.existsUnique_isLocalInv p ζ hζ q
  have hex : ∃ f : H →ₗ[ZMod p] ZMod p, IsLocalInv p ζ q f ∧ ∀ f', IsLocalInv p ζ q f' → f' = f := ⟨f, hf, hfu⟩
  have hloc : localInv p ζ q = f := by
    unfold localInv
    rw [dif_pos hex]
    exact hfu _ (Classical.choose_spec hex).1
  rw [hloc]
  refine ⟨hf, ?_⟩

  obtain ⟨u, hu, φ, hs, hfin, hfrob, π, hπ, hN, z, hz, hcong, -⟩ :=
    groupCohomology.exists_levelCocycles2_ofChar_cycloChar_isLocalInv_witness p ζ hζ q
  have hfe : f (continuousH2π (primeLocalToGlobal q) Mμ ⟨z, hz⟩) = 1 := hf u hu φ hs hfin hfrob π hπ hN z hz hcong
  obtain ⟨hfinH, hrankH⟩ := groupCohomology.finrank_continuousH2_ofChar_cycloChar_of_primeLocal (p := p) q
  haveI : FiniteDimensional (ZMod p) H := hfinH
  have hsurj : Function.Surjective f := fun c =>
    ⟨c • continuousH2π (primeLocalToGlobal q) Mμ ⟨z, hz⟩, by rw [map_smul, hfe, smul_eq_mul, mul_one]⟩
  have hinj : Function.Injective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by rw [hrankH, Module.finrank_self])).2 hsurj
  exact ⟨hinj, hsurj⟩

end S_groupCohomology_isLocalInv_localInv_and_bijective
end P2MW
export P2MW.S_groupCohomology_isLocalInv_localInv_and_bijective (solution)
