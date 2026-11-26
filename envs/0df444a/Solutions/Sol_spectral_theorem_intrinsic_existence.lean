-- Prove2me | solution 1 for spectral_theorem_intrinsic_existence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:13:49.84799+00:00
-- url     : https://prove2.me/submissions/ac7efa1d-214a-4d0e-82f1-39d2a11baf9a

import Definitions.Def_Spectral_Spectral_Uniqueness
import Definitions.Def_Spectral_Spectral_Intrinsic
import Theorems.Thm_PVM_represents_of_unboundedIntegral_eq
import Theorems.Thm_spectral_theorem_existence


set_option autoImplicit false
open MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution
    (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A) :
    ∃ E_pvm : PVM E, E_pvm.Represents A := by
  rcases spectral_theorem_existence A hA with ⟨E_pvm, hrep⟩
  exact ⟨E_pvm, E_pvm.represents_of_unboundedIntegral_eq A hrep⟩
