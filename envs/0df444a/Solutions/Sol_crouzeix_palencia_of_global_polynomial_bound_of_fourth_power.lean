-- Prove2me | solution 1 for crouzeix_palencia_of_global_polynomial_bound_of_fourth_power
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:20:18.587921+00:00
-- url     : https://prove2.me/submissions/99485094-7fe4-41cc-b97b-5b3c5b43b9c6

import Definitions.Def_Operator_Crouzeix_AuxOperator
import Definitions.Def_Operator_SpectralSet_Normal
import Definitions.Def_Operator_Crouzeix_Palencia
import Theorems.Thm_le_one_add_sqrt_two_of_fourth_le_two_mul_cube_add_sq
import Theorems.Thm_polynomialSupNorm_nonneg
import Theorems.Thm_spectrum_subset_closure_numericalRange


set_option autoImplicit false
open scoped InnerProductSpace
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) (K : ℝ) (hK : 0 ≤ K)
    (hfour : K ^ 4 ≤ 2 * K ^ 3 + K ^ 2)
    (hcalc : ∀ p : Polynomial ℂ,
      ‖Polynomial.aeval A p‖ ≤
        K * polynomialSupNorm p (closure (numericalRange A))) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by
  refine ⟨spectrum_subset_closure_numericalRange A, ?_⟩
  intro p
  have hfixed :=
    le_one_add_sqrt_two_of_fourth_le_two_mul_cube_add_sq hK hfour
  exact (hcalc p).trans (mul_le_mul_of_nonneg_right hfixed
    (polynomialSupNorm_nonneg p (closure (numericalRange A))))
