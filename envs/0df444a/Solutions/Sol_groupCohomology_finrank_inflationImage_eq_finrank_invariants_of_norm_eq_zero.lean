-- Prove2me | solution 1 for groupCohomology.finrank_inflationImage_eq_finrank_invariants_of_norm_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/26931648-c2f3-5d1a-8887-9159d86f7a04

import Mathlib
import Definitions.Def_GroupCohomology_LocallyConstantClasses
import Theorems.Thm_groupCohomology_finrank_H1_eq_finrank_invariants_of_norm_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_finrank_inflationImage_eq_finrank_invariants_of_norm_eq_zero

open CategoryTheory Module groupCohomology

universe u

namespace Ws14Port

def invariantsQuotientToInvariantsEquiv' {k G : Type u} [CommRing k] [Group G] (A : Rep k G) (S : Subgroup G) [S.Normal] :
    (A.quotientToInvariants S).ρ.invariants ≃ₗ[k] A.ρ.invariants where
  toFun x := ⟨x.1.1, fun g => congrArg Subtype.val (x.2 (QuotientGroup.mk g))⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun y := ⟨⟨y.1, fun s => y.2 s.1⟩, fun q => QuotientGroup.induction_on q
    fun g => Subtype.ext (y.2 g)⟩
  left_inv _ := Subtype.ext (Subtype.ext rfl)
  right_inv _ := rfl

theorem finrank_inflationImage_eq_finrank_H1_quot {k G : Type u} [Field k] [Group G] (M : Rep k G) (N : Subgroup G) [N.Normal] :
    Module.finrank k (groupCohomology.inflationImage M N) = Module.finrank k (groupCohomology.H1 (M.quotientToInvariants N)) := by
  show Module.finrank k (LinearMap.range (groupCohomology.inflation M N).hom) = _
  rw [groupCohomology.inflation_eq_H1InfRes_f]
  exact LinearMap.finrank_range_of_inj ((ModuleCat.mono_iff_injective _).1 (inferInstance : Mono (H1InfRes M N).f))

end Ws14Port

theorem solution
    {k G : Type u} [Field k] [Group G] (M : Rep k G) [FiniteDimensional k M]
    (N : Subgroup G) [N.Normal] [Fintype (G ⧸ N)]
    {φ : G} (hφ : ∀ x : G ⧸ N, x ∈ Subgroup.zpowers (QuotientGroup.mk φ : G ⧸ N))
    (hN : (M.quotientToInvariants N).ρ.norm = 0) :
    Module.finrank k (groupCohomology.inflationImage M N) = Module.finrank k M.ρ.invariants := by
  haveI hfd : FiniteDimensional k (M.quotientToInvariants N) :=
    inferInstanceAs (FiniteDimensional k (Representation.invariants (M.ρ.comp N.subtype)))
  rw [Ws14Port.finrank_inflationImage_eq_finrank_H1_quot,
    groupCohomology.finrank_H1_eq_finrank_invariants_of_norm_eq_zero (M.quotientToInvariants N) hφ hN,
    (Ws14Port.invariantsQuotientToInvariantsEquiv' M N).finrank_eq]

end S_groupCohomology_finrank_inflationImage_eq_finrank_invariants_of_norm_eq_zero
end P2MW
export P2MW.S_groupCohomology_finrank_inflationImage_eq_finrank_invariants_of_norm_eq_zero (solution)
