-- Prove2me | solution 1 for groupCohomology.finrank_finiteQuotientH1_eq_invariants_add_dualTwist_of_primeLocal_ne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/c404e5fd-2695-59c4-96e2-2ad625b7790c

import Mathlib
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Theorems.Thm_groupCohomology_finrank_continuousClasses_le_invariants_add_dualTwist
import Theorems.Thm_groupCohomology_invariants_add_dualTwist_le_finrank_continuousClasses
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_finrank_finiteQuotientH1_eq_invariants_add_dualTwist_of_primeLocal_ne
p2m_attr_erase "instance" "ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO"
p2m_attr_erase "simp" "groupCohomology.frobeniusOnCoinvariants_mk groupCohomology.evalAtGen_apply ExtCitation.LocalLevel.coe_smul_OO"

set_option autoImplicit false
open CategoryTheory Module groupCohomology ExtCitation

theorem solution
    {p : ℕ} [Fact p.Prime] (q : Nat.Primes) (hne : (q : ℕ) ≠ p)
    (M : Rep (ZMod p) (primeLocalGaloisGroup q))
    [FiniteDimensional (ZMod p) M]
    (hsm : ∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ),
      FiniteDimensional ℚ F ∧
        ∀ s, primeLocalToGlobal q s ∈ F.fixingSubgroup → M.ρ s m = m)
    (adm₁ : Submodule (ZMod p) (H1 M)) [FiniteDimensional (ZMod p) adm₁]
    (hadm₁ : ∀ x, x ∈ adm₁ ↔ ∃ c : cocycles₁ M,
      (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
        ∀ (g s : primeLocalGaloisGroup q),
          primeLocalToGlobal q s ∈ F.fixingSubgroup → c.val (g * s) = c.val g)
      ∧ (H1π M).hom c = x) :
    finrank (ZMod p) adm₁
      = finrank (ZMod p) M.ρ.invariants
        + finrank (ZMod p)
            (M.dualTwist ((cycloChar p).comp (primeLocalToGlobal q))).ρ.invariants := by
  exact le_antisymm
    (groupCohomology.finrank_continuousClasses_le_invariants_add_dualTwist q hne M hsm adm₁ hadm₁)
    (groupCohomology.invariants_add_dualTwist_le_finrank_continuousClasses q hne M hsm adm₁ hadm₁)

end S_groupCohomology_finrank_finiteQuotientH1_eq_invariants_add_dualTwist_of_primeLocal_ne
end P2MW
export P2MW.S_groupCohomology_finrank_finiteQuotientH1_eq_invariants_add_dualTwist_of_primeLocal_ne (solution)
