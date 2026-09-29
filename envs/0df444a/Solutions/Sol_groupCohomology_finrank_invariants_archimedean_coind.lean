-- Prove2me | solution 1 for groupCohomology.finrank_invariants_archimedean_coind
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/08200f0b-3a32-5215-8f75-63a10ab2a85e

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import Theorems.Thm_Rep_finrank_invariants_res_coind_eq_finsum
import Theorems.Thm_Rep_invariants_res_eq_invariants_res_range
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_finrank_invariants_archimedean_coind

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory Module groupCohomology ExtCitation"
open scoped Classical

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 1600000
set_option Elab.async false

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory Module groupCohomology ExtCitation"
open scoped Classical

local instance CycBaseMackeyInf.isAlgebraicQbar : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) :=
  AlgebraicClosure.isAlgebraic ℚ
local instance CycBaseMackeyInf.isAlgClosureQbar : IsAlgClosure ℚ (AlgebraicClosure ℚ) :=
  ⟨inferInstance, inferInstance⟩
local instance CycBaseMackeyInf.isGaloisQbar : IsGalois ℚ (AlgebraicClosure ℚ) :=
  IsAlgClosure.isGalois ℚ (AlgebraicClosure ℚ)
local instance CycBaseMackeyInf.normalQbar : Normal ℚ (AlgebraicClosure ℚ) :=
  IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)

namespace CycBaseMackeyInf

theorem finite_quotient_fixingSubgroup (E : IntermediateField ℚ (AlgebraicClosure ℚ))
    [FiniteDimensional ℚ E] :
    Finite ((AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ⧸ E.fixingSubgroup) :=
  Subgroup.quotient_finite_of_isOpen _ (IntermediateField.fixingSubgroup_isOpen E)

theorem finiteIndex_fixingSubgroup (E : IntermediateField ℚ (AlgebraicClosure ℚ))
    [FiniteDimensional ℚ E] : E.fixingSubgroup.FiniteIndex :=
  haveI := finite_quotient_fixingSubgroup E
  Subgroup.finiteIndex_of_finite_quotient

end CycBaseMackeyInf

theorem solution
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (N : Rep.{0} (ZMod p) ↥K.fixingSubgroup) [FiniteDimensional (ZMod p) N] :
    Module.finrank (ZMod p) (Rep.res (extArithLoc S (Sum.inl ())) (Rep.coind K.fixingSubgroup.subtype N)).ρ.invariants =
      ∑ᶠ v : Quotient (MulAction.orbitRel ↥K.fixingSubgroup
          ((AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ⧸ (extArithLoc S (Sum.inl ())).range)),
        Module.finrank (ZMod p) (Rep.res (MulAction.stabilizer (↥K.fixingSubgroup) v.out).subtype N).ρ.invariants := by
  haveI : K.fixingSubgroup.FiniteIndex := CycBaseMackeyInf.finiteIndex_fixingSubgroup K
  rw [Rep.invariants_res_eq_invariants_res_range (extArithLoc S (Sum.inl ()))
    (Rep.coind K.fixingSubgroup.subtype N)]
  exact Rep.finrank_invariants_res_coind_eq_finsum K.fixingSubgroup
    (extArithLoc S (Sum.inl ())).range N

end S_groupCohomology_finrank_invariants_archimedean_coind
end P2MW
export P2MW.S_groupCohomology_finrank_invariants_archimedean_coind (solution)
