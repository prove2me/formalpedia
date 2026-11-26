-- Prove2me | solution 1 for crouzeix_palencia_of_auxiliary_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:36:16.272283+00:00
-- url     : https://prove2.me/submissions/9d8843de-2dc5-4d1b-8e4f-2d53e59edf02

import Definitions.Def_Operator_Crouzeix_AuxOperator
import Definitions.Def_Operator_SpectralSet_Normal
import Definitions.Def_Operator_Crouzeix_Palencia
import Theorems.Thm_norm_le_one_add_sqrt_two_mul_of_auxiliary_bounds
import Theorems.Thm_spectrum_subset_closure_numericalRange


set_option autoImplicit false
open scoped InnerProductSpace
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E]
theorem _root_.solution (A : E →L[ℂ] E)
    (haux : ∀ p : Polynomial ℂ, ∃ G : E →L[ℂ] E,
      ‖Polynomial.aeval A p + star G‖ ≤
        2 * polynomialSupNorm p (closure (numericalRange A)) ∧
      ‖Polynomial.aeval A p * G‖ ≤
        polynomialSupNorm p (closure (numericalRange A)) ^ 2) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2) (closure (numericalRange A)) := by
  constructor
  · exact spectrum_subset_closure_numericalRange A
  · intro p
    obtain ⟨G, hsymm, hprod⟩ := haux p
    exact norm_le_one_add_sqrt_two_mul_of_auxiliary_bounds
      (Polynomial.aeval A p) G hsymm hprod
