-- Prove2me | solution 1 for norm_cayleyTransform
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:52:43.697847+00:00
-- url     : https://prove2.me/submissions/b534966f-71e0-413f-8fbb-a18ece73630b

import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Definitions.Def_Spectral_Cayley_Basic

set_option autoImplicit false
open scoped LinearPMap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A)
    (y : E) : ‖cayleyTransform A hA y‖ = ‖y‖ := by
  let e := LinearEquiv.ofBijective (plusI A) ⟨plusI_injective A hA, plusI_surjective A hA⟩
  let x : A.domain := e.symm y
  have hplus : plusI A x = y := by
    change e x = y
    exact e.apply_symm_apply y
  have hnorm : ‖minusI A x‖ = ‖plusI A x‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [minusI_norm_sq A hA, plusI_norm_sq A hA]
  change ‖minusI A x‖ = ‖y‖
  rw [hnorm, hplus]
