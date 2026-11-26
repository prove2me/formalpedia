-- Prove2me | solution 1 for spectral_theorem_intrinsic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:15:53.171651+00:00
-- url     : https://prove2.me/submissions/df577d1d-4b47-4ab6-9e0a-58d7ff891d7c

import Definitions.Def_Spectral_Spectral_Uniqueness
import Definitions.Def_Spectral_Spectral_Intrinsic
import Theorems.Thm_spectral_theorem_intrinsic_existence
import Theorems.Thm_PVM_Represents_proj_eq_on_measurable

set_option autoImplicit false
open MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution
    (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A) :
    ∃ E_pvm : PVM E,
      E_pvm.Represents A ∧
      ∀ F_pvm : PVM E, F_pvm.Represents A →
        ∀ S : Set ℝ, MeasurableSet S → E_pvm.proj S = F_pvm.proj S := by
  rcases spectral_theorem_intrinsic_existence A hA with ⟨E_pvm, hrep⟩
  refine ⟨E_pvm, hrep, ?_⟩
  intro F_pvm hF S hS
  exact hrep.proj_eq_on_measurable hA hF S hS
