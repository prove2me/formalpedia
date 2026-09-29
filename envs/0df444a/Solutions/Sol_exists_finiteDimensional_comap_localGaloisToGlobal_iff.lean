-- Prove2me | solution 1 for exists_finiteDimensional_comap_localGaloisToGlobal_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/dd86b01f-92f0-5621-a2ab-056c871da208

import Definitions.Def_GaloisRep_CompletionBridge
import Theorems.Thm_IntermediateField_finiteDimensional_adjoin_padicEmbedding_image
import Theorems.Thm_localGaloisToGlobal_mem_fixingSubgroup_iff
import Theorems.Thm_IntermediateField_exists_le_adjoin_padicEmbedding_image
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_exists_finiteDimensional_comap_localGaloisToGlobal_iff

set_option autoImplicit false
open scoped IntermediateField
open Polynomial
open scoped Pointwise

theorem solution
    (q : ℕ) [Fact q.Prime]
    (P : Subgroup (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q) → Prop)
    (hP : ∀ U V, V ≤ U → P U → P V) :
    (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
        P (F.fixingSubgroup.comap (localGaloisToGlobal q))) ↔
      ∃ K : IntermediateField ℚ_[q] (PadicAlgCl q), FiniteDimensional ℚ_[q] K ∧
        P K.fixingSubgroup := by
  constructor
  · rintro ⟨F, hF, h⟩
    refine ⟨IntermediateField.adjoin ℚ_[q] (padicEmbedding q '' (F : Set (AlgebraicClosure ℚ))),
      IntermediateField.finiteDimensional_adjoin_padicEmbedding_image q F, hP _ _ ?_ h⟩
    intro s hs
    rw [Subgroup.mem_comap]
    exact (localGaloisToGlobal_mem_fixingSubgroup_iff q F s).mpr hs
  · rintro ⟨K, hK, h⟩
    obtain ⟨F, hF, hKF⟩ := IntermediateField.exists_le_adjoin_padicEmbedding_image q K
    refine ⟨F, hF, hP _ _ ?_ h⟩
    intro s hs
    exact IntermediateField.fixingSubgroup_antitone hKF
      ((localGaloisToGlobal_mem_fixingSubgroup_iff q F s).mp hs)

end S_exists_finiteDimensional_comap_localGaloisToGlobal_iff
end P2MW
export P2MW.S_exists_finiteDimensional_comap_localGaloisToGlobal_iff (solution)
