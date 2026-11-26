-- Prove2me | solution 1 for crouzeix_palencia_of_finite_global_bound_of_uniform_fourth_power_improvement
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:20:23.434436+00:00
-- url     : https://prove2.me/submissions/70806b29-c044-4b68-902a-4fa6f10a3392

import Definitions.Def_Operator_Crouzeix_AuxOperator
import Definitions.Def_Operator_SpectralSet_Normal
import Definitions.Def_Operator_Crouzeix_Palencia
import Theorems.Thm_isKPolynomialSpectralSet_of_finite_global_bound_of_uniform_fourth_power_improvement
import Theorems.Thm_spectrum_subset_closure_numericalRange


set_option autoImplicit false
open scoped InnerProductSpace
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E)
    (hfinite : ∃ K : ℝ, 0 ≤ K ∧ ∀ p : Polynomial ℂ,
      ‖Polynomial.aeval A p‖ ≤
        K * polynomialSupNorm p (closure (numericalRange A)))
    (hfour : ∀ K : ℝ, 0 ≤ K →
      (∀ p : Polynomial ℂ, ‖Polynomial.aeval A p‖ ≤
        K * polynomialSupNorm p (closure (numericalRange A))) →
      ∀ p : Polynomial ℂ,
        ‖Polynomial.aeval A p‖ ^ 4 ≤
          (2 * K ^ 3 + K ^ 2) *
            polynomialSupNorm p (closure (numericalRange A)) ^ 4) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by
  exact
    isKPolynomialSpectralSet_of_finite_global_bound_of_uniform_fourth_power_improvement
      A (closure (numericalRange A))
        (spectrum_subset_closure_numericalRange A) hfinite hfour
