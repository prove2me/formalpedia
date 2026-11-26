-- Prove2me | solution 1 for selfAdjoint_generates_unitary_group_generator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:12:07.213142+00:00
-- url     : https://prove2.me/submissions/e2e87608-47a9-4aab-b383-3355a844016e

import Definitions.Def_Spectral_Stone_SelfAdjoint
import Definitions.Def_Spectral_Spectral_Existence
import Definitions.Def_Spectral_Stone_Theorem
import Theorems.Thm_PVM_phaseUnitaryGroup_generator
import Theorems.Thm_spectral_theorem_existence


set_option autoImplicit false
open MeasureTheory Filter
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution
    (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A) :
    (selfAdjoint_generates_unitary_group A hA).generator = A := by
  unfold selfAdjoint_generates_unitary_group
  rw [PVM.phaseUnitaryGroup_generator]
  exact Classical.choose_spec (spectral_theorem_existence A hA)
