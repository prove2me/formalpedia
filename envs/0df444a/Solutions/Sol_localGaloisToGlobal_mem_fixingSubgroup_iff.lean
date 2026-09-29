-- Prove2me | solution 1 for localGaloisToGlobal_mem_fixingSubgroup_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/0a6fdc5a-2ba6-5755-9b20-9b8f805c447a

import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_localGaloisToGlobal_mem_fixingSubgroup_iff

set_option autoImplicit false
open scoped IntermediateField
open Polynomial
open scoped Pointwise

theorem solution
    (q : ℕ) [Fact q.Prime]
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) (s : PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q) :
    localGaloisToGlobal q s ∈ F.fixingSubgroup ↔
      s ∈ (IntermediateField.adjoin ℚ_[q]
        (padicEmbedding q '' (F : Set (AlgebraicClosure ℚ)))).fixingSubgroup := by
  rw [IntermediateField.mem_fixingSubgroup_iff, IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h x hx
    induction hx using IntermediateField.adjoin_induction with
    | mem y hy =>
      obtain ⟨z, hz, rfl⟩ := hy
      rw [← padicEmbedding_localGaloisToGlobal, h z hz]
    | algebraMap c => exact s.commutes c
    | add y z _ _ hy hz => rw [map_add, hy, hz]
    | mul y z _ _ hy hz => rw [map_mul, hy, hz]
    | inv y _ hy => rw [map_inv₀, hy]
  · intro h x hx
    have hfix := h (padicEmbedding q x) (IntermediateField.subset_adjoin _ _ ⟨x, hx, rfl⟩)
    rw [← padicEmbedding_localGaloisToGlobal] at hfix
    exact (padicEmbedding q : AlgebraicClosure ℚ →+* PadicAlgCl q).injective hfix

end S_localGaloisToGlobal_mem_fixingSubgroup_iff
end P2MW
export P2MW.S_localGaloisToGlobal_mem_fixingSubgroup_iff (solution)
