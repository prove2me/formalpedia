-- Prove2me | solution 1 for groupCohomology.finrank_inflationImage_eq_finrank_invariants
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/0ff669ce-20de-56b5-a85b-bd0af273801b

import Mathlib
import Definitions.Def_GroupCohomology_LocallyConstantClasses
import Theorems.Thm_groupCohomology_finrank_inflationImage_eq_finrank_H1_quotientToInvariants
import Theorems.Thm_groupCohomology_finrank_H1_eq_finrank_invariants_of_norm_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_finrank_inflationImage_eq_finrank_invariants

open CategoryTheory Module groupCohomology

universe u

namespace Ws14Port

def invariantsQuotientToInvariantsEquiv {k G : Type u} [CommRing k] [Group G] (A : Rep k G) (S : Subgroup G) [S.Normal] :
    (A.quotientToInvariants S).ρ.invariants ≃ₗ[k] A.ρ.invariants where
  toFun x := ⟨x.1.1, fun g => congrArg Subtype.val (x.2 (QuotientGroup.mk g))⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun y := ⟨⟨y.1, fun s => y.2 s.1⟩, fun q => QuotientGroup.induction_on q
    fun g => Subtype.ext (y.2 g)⟩
  left_inv _ := Subtype.ext (Subtype.ext rfl)
  right_inv _ := rfl

end Ws14Port

theorem solution {k G : Type u} [Field k] [Group G] (A : Rep k G) (S : Subgroup G) [S.Normal]
    [Finite G] [Fintype (G ⧸ S)] [FiniteDimensional k A]
    {φ : G} (hφ : ∀ x : G ⧸ S, x ∈ Subgroup.zpowers (QuotientGroup.mk φ : G ⧸ S))
    (hN : (A.quotientToInvariants S).ρ.norm = 0) :
    finrank k (inflationImage A S) = finrank k A.ρ.invariants := by
  haveI hfd : FiniteDimensional k (A.quotientToInvariants S) :=
    inferInstanceAs (FiniteDimensional k (Representation.invariants (A.ρ.comp S.subtype)))
  rw [groupCohomology.finrank_inflationImage_eq_finrank_H1_quotientToInvariants,
    groupCohomology.finrank_H1_eq_finrank_invariants_of_norm_eq_zero (A.quotientToInvariants S) hφ hN,
    (Ws14Port.invariantsQuotientToInvariantsEquiv A S).finrank_eq]

end S_groupCohomology_finrank_inflationImage_eq_finrank_invariants
end P2MW
export P2MW.S_groupCohomology_finrank_inflationImage_eq_finrank_invariants (solution)
