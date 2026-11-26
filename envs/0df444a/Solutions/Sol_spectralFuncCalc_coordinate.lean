-- Prove2me | solution 1 for spectralFuncCalc_coordinate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:10:25.597591+00:00
-- url     : https://prove2.me/submissions/1534009f-a60c-4a91-9965-22a2cab850c7

import Definitions.Def_Spectral_Spectral_Existence
import Definitions.Def_Spectral_PVM_Unbounded
import Definitions.Def_Spectral_Spectral_FuncCalc
import Theorems.Thm_spectral_theorem_existence


set_option autoImplicit false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution
    (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A) :
    spectralFuncCalc A hA ((↑) : ℝ → ℂ)
      Complex.continuous_ofReal.measurable = A := by
  unfold spectralFuncCalc
  exact Classical.choose_spec (spectral_theorem_existence A hA)
