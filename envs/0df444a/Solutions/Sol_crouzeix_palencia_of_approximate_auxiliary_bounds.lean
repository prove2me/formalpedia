-- Prove2me | solution 1 for crouzeix_palencia_of_approximate_auxiliary_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:21:14.686827+00:00
-- url     : https://prove2.me/submissions/b475a4c2-9a06-4faf-a38b-1d354aecaf31

import Definitions.Def_Operator_Crouzeix_Palencia
import Definitions.Def_Operator_Crouzeix_PalenciaApproximation
import Theorems.Thm_norm_le_one_add_sqrt_two_mul_of_approximate_auxiliary_bounds
import Theorems.Thm_spectrum_subset_closure_numericalRange


set_option autoImplicit false
open Filter
open scoped InnerProductSpace
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E)
    (haux : ∀ (p : Polynomial ℂ) (ε : ℝ), 0 < ε →
      ∃ G : E →L[ℂ] E,
        ‖Polynomial.aeval A p + star G‖ ≤
            2 * (polynomialSupNorm p (closure (numericalRange A)) + ε) ∧
        ‖Polynomial.aeval A p * G‖ ≤
            (polynomialSupNorm p (closure (numericalRange A)) + ε) ^ 2) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by
  constructor
  · exact spectrum_subset_closure_numericalRange A
  · intro p
    exact norm_le_one_add_sqrt_two_mul_of_approximate_auxiliary_bounds
      (Polynomial.aeval A p) (fun ε hε => haux p ε hε)
