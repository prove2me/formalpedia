-- Prove2me | solution 1 for groupCohomology.bijective_of_isTheta1_localInv_extArithLoc
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/f926034a-a0fe-54cd-9b7c-592e0d217817

import Mathlib
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GroupCohomology_ContinuousDuality
import Definitions.Def_GroupCohomology_LocalInvariant
import Theorems.Thm_groupCohomology_bijective_theta_dualTwist_of_primeLocal
import Theorems.Thm_groupCohomology_exists_theta0_and_theta2
import Theorems.Thm_groupCohomology_isLocalInv_localInv_and_bijective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_bijective_of_isTheta1_localInv_extArithLoc
p2m_attr_erase "instance" "ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal groupCohomology.normal_comap_fixingSubgroup groupCohomology.finiteIndex_comap_fixingSubgroup ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete groupCohomology.Kummer.instMulDistribMulActionRootsOfUnity"
p2m_attr_erase "simp" "ExtCitation.LocalLevel.coe_smul_OO WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply groupCohomology.Kummer.coe_kummerCocycleRoots groupCohomology.Kummer.mem_powerSubgroup_iff groupCohomology.Kummer.val_smul_units groupCohomology.Kummer.kummerHom_apply groupCohomology.Kummer.coe_smul_rootsOfUnity IsLocalRing.principalUnits_zero"
set_option autoImplicit false
open CategoryTheory groupCohomology ExtCitation

namespace Pen5Theta1

theorem eval_isEquivariantBilinear {k G : Type} [Field k] [Group G] (A : Rep.{0} k G) (χ : G →* kˣ) :
    Rep.IsEquivariantBilinear A (A.dualTwist χ) (ofChar (k := k) χ)
      (Module.Dual.eval k A : A →ₗ[k] A.dualTwist χ →ₗ[k] ofChar (k := k) χ) := by
  intro g a b
  simp [Representation.twist_apply_apply, Module.Dual.eval_apply, Module.Dual.transpose_apply,
    ← Module.End.mul_apply, ← map_mul]

theorem dual_twist_comp {k G H V : Type} [Field k] [Group G] [Group H] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) (χ : G →* kˣ) (f : H →* G) :
    Representation.twist (Representation.dual (ρ.comp f)) (χ.comp f) = (ρ.dual.twist χ).comp f := by
  refine MonoidHom.ext fun g => LinearMap.ext fun x => ?_
  simp [Representation.twist_apply_apply, Representation.dual_apply, map_inv]

theorem bijective_of_isTheta1_of_eq
    {p : ℕ} [Fact p.Prime] (q : Nat.Primes) [Fact ((q : ℕ)).Prime]
    (A : Rep.{0} (ZMod p) (primeLocalGaloisGroup q)) [FiniteDimensional (ZMod p) A]
    (hsm : ∀ m : A, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s, primeLocalToGlobal q s ∈ F.fixingSubgroup → A.ρ s m = m)
    (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p)
    (ρD : Representation (ZMod p) (primeLocalGaloisGroup q) (Module.Dual (ZMod p) A))
    (hρ : A.ρ.dual.twist ((cycloChar p).comp (primeLocalToGlobal q)) = ρD)
    (θ : continuousH1 (primeLocalToGlobal q) A →ₗ[ZMod p]
      Module.Dual (ZMod p) (continuousH1 (primeLocalToGlobal q) (Rep.of ρD)))
    (hθ : IsTheta1 (primeLocalToGlobal q)
      (Module.Dual.eval (ZMod p) A :
        A →ₗ[ZMod p] Rep.of ρD →ₗ[ZMod p] ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))
      (localInv p ζ q) θ) :
    Function.Bijective θ := by
  subst hρ
  obtain ⟨-, hinv⟩ := groupCohomology.isLocalInv_localInv_and_bijective p ζ hζ q
  have hex := @groupCohomology.exists_theta0_and_theta2 (ZMod p) (primeLocalGaloisGroup q) _ _
    (primeLocalToGlobal q) A (A.dualTwist ((cycloChar p).comp (primeLocalToGlobal q)))
    (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))
    (Module.Dual.eval (ZMod p) A :
      A →ₗ[ZMod p] A.dualTwist ((cycloChar p).comp (primeLocalToGlobal q)) →ₗ[ZMod p]
        ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))
    (eval_isEquivariantBilinear A ((cycloChar p).comp (primeLocalToGlobal q))) (localInv p ζ q)
  obtain ⟨⟨θ₀, hθ₀⟩, ⟨θ₂, hθ₂⟩⟩ := hex
  exact (groupCohomology.bijective_theta_dualTwist_of_primeLocal q A hsm (localInv p ζ q) hinv
    θ₀ hθ₀ θ hθ θ₂ hθ₂).2.1

end Pen5Theta1

open Pen5Theta1 in
theorem solution
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (q : ↥S)
    (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) [FiniteDimensional (ZMod p) M]
    (hsm : ∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s ∈ F.fixingSubgroup, M.ρ s m = m)
    (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p)
    (θ : continuousH1 (extArithLoc S (Sum.inr q)) (Rep.res (extArithLoc S (Sum.inr q)) M) →ₗ[ZMod p]
        Module.Dual (ZMod p)
          (continuousH1 (extArithLoc S (Sum.inr q)) (Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p)))))
    (hθ :
      haveI : Fact (((q : Nat.Primes) : ℕ)).Prime := ⟨(q : Nat.Primes).prop⟩
      IsTheta1 (extArithLoc S (Sum.inr q))
        (Module.Dual.eval (ZMod p) M :
          Rep.res (extArithLoc S (Sum.inr q)) M →ₗ[ZMod p]
            Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p)) →ₗ[ZMod p]
              ofChar (k := ZMod p) ((cycloChar p).comp (extArithLoc S (Sum.inr q))))
        (localInv p ζ (q : Nat.Primes)) θ) :
    Function.Bijective θ := by
  haveI : Fact (((q : Nat.Primes) : ℕ)).Prime := ⟨(q : Nat.Primes).prop⟩
  exact bijective_of_isTheta1_of_eq (q : Nat.Primes) (Rep.res (primeLocalToGlobal (q : Nat.Primes)) M)
    (fun m => by
      obtain ⟨F, hF, h⟩ := hsm m
      exact ⟨F, hF, fun s hs => h _ hs⟩)
    ζ hζ ((M.ρ.dual.twist (cycloChar p)).comp (primeLocalToGlobal (q : Nat.Primes)))
    (dual_twist_comp M.ρ (cycloChar p) (primeLocalToGlobal (q : Nat.Primes))) θ hθ

end S_groupCohomology_bijective_of_isTheta1_localInv_extArithLoc
end P2MW
export P2MW.S_groupCohomology_bijective_of_isTheta1_localInv_extArithLoc (solution)
