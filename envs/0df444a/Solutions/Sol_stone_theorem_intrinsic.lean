-- Prove2me | solution 1 for stone_theorem_intrinsic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:12:55.119858+00:00
-- url     : https://prove2.me/submissions/af7e5107-cbf4-4e17-ac4a-a126f459d218

import Definitions.Def_Spectral_Stone_Theorem
import Definitions.Def_Spectral_Stone_Intrinsic
import Theorems.Thm_StrongContUnitary_generator_isSelfAdjoint
import Theorems.Thm_StrongContUnitary_mem_generator_domain_iff
import Theorems.Thm_StrongContUnitary_tendsto_generator
import Theorems.Thm_selfAdjoint_generates_unitary_group_generator

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
private theorem StrongContUnitary.generates_generator
    (U : StrongContUnitary E) : U.Generates U.generator :=
  ⟨U.mem_generator_domain_iff, U.tendsto_generator⟩
end

set_option autoImplicit false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution :
    (∀ U : StrongContUnitary E, ∃ A : E →ₗ.[ℂ] E,
      IsSelfAdjoint A ∧ U.Generates A) ∧
    (∀ A : E →ₗ.[ℂ] E, IsSelfAdjoint A →
      ∃ U : StrongContUnitary E, U.Generates A) := by
  constructor
  · intro U
    exact ⟨U.generator, U.generator_isSelfAdjoint, U.generates_generator⟩
  · intro A hA
    let U := selfAdjoint_generates_unitary_group A hA
    refine ⟨U, ?_⟩
    rw [← selfAdjoint_generates_unitary_group_generator A hA]
    exact U.generates_generator
