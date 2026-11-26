-- Prove2me | solution 1 for crouzeix_palencia_of_polynomial_auxiliary_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:21:05.749103+00:00
-- url     : https://prove2.me/submissions/53d996ff-8a57-47b6-bf21-386293f3705c

import Definitions.Def_Operator_Crouzeix_AuxOperator
import Definitions.Def_Operator_SpectralSet_Normal
import Definitions.Def_Operator_Crouzeix_Palencia
import Theorems.Thm_crouzeix_palencia_of_auxiliary_bounds

set_option autoImplicit false
open scoped InnerProductSpace
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain)
    (hbounds : ∀ p : Polynomial ℂ,
      ‖Polynomial.aeval A p + star (crouzeixPolynomialAuxiliaryOperator A Omega p)‖ ≤
        2 * polynomialSupNorm p (closure (numericalRange A)) ∧
      ‖Polynomial.aeval A p * crouzeixPolynomialAuxiliaryOperator A Omega p‖ ≤
        polynomialSupNorm p (closure (numericalRange A)) ^ 2) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2) (closure (numericalRange A)) := by
  apply crouzeix_palencia_of_auxiliary_bounds A
  intro p
  exact ⟨crouzeixPolynomialAuxiliaryOperator A Omega p, hbounds p⟩
