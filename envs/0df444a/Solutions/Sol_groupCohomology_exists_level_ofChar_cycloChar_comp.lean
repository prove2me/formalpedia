-- Prove2me | solution 1 for groupCohomology.exists_level_ofChar_cycloChar_comp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/8baa921b-16fb-50c3-84a4-a2ca46feca9e

import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Theorems.Thm_ExtCitation_cycloChar_eq_one_of_apply_eq_self_of_isPrimitiveRoot
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_exists_level_ofChar_cycloChar_comp

set_option autoImplicit false
open CategoryTheory groupCohomology ExtCitation
open scoped IntermediateField Pointwise

theorem solution
    {p : ℕ} [Fact p.Prime] {G : Type} [Group G] (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (m : ofChar (k := ZMod p) ((cycloChar p).comp r)) :
    ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s, r s ∈ F.fixingSubgroup → (ofChar (k := ZMod p) ((cycloChar p).comp r)).ρ s m = m := by
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  haveI : NeZero p := ⟨hp0⟩
  haveI : NeZero (p : AlgebraicClosure ℚ) := ⟨Nat.cast_ne_zero.mpr hp0⟩
  obtain ⟨ξ, hξ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) p
  haveI : FiniteDimensional ℚ ℚ⟮ξ⟯ :=
    IntermediateField.adjoin.finiteDimensional (((AlgebraicClosure.isAlgebraic ℚ).isAlgebraic ξ).isIntegral)
  refine ⟨ℚ⟮ξ⟯, inferInstance, fun s hs => ?_⟩
  have hfix : r s ξ = ξ :=
    (IntermediateField.mem_fixingSubgroup_iff _ _).mp hs ξ (IntermediateField.mem_adjoin_simple_self ℚ ξ)
  have h1 : cycloChar p (r s) = 1 := cycloChar_eq_one_of_apply_eq_self_of_isPrimitiveRoot p (r s) hξ hfix
  show (((cycloChar p).comp r s : (ZMod p)ˣ) : ZMod p) * m = m
  rw [MonoidHom.comp_apply, h1, Units.val_one, one_mul]

end S_groupCohomology_exists_level_ofChar_cycloChar_comp
end P2MW
export P2MW.S_groupCohomology_exists_level_ofChar_cycloChar_comp (solution)
