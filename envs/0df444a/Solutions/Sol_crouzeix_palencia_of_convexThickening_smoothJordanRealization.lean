-- Prove2me | solution 1 for crouzeix_palencia_of_convexThickening_smoothJordanRealization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:38:39.890875+00:00
-- url     : https://prove2.me/submissions/10038c34-6b8b-4db3-9ce9-ed9a49d04745

import Definitions.Def_Operator_Crouzeix_SmoothJordanMergelyan
import Definitions.Def_Operator_Crouzeix_SmoothJordanMergelyanAssembly
import Theorems.Thm_SmoothJordanDomain_hasMergelyanPolynomialApproximation
import Theorems.Thm_crouzeix_palencia_of_convexThickening_hasMergelyanPolynomialApproximation


set_option autoImplicit false
open Complex Set
open scoped InnerProductSpace
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) (Omega : ℕ → SmoothJordanDomain)
    (hcarrier : ∀ n, (Omega n).carrier =
      convexThickeningApprox (closure (numericalRange A)) n) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by
  apply crouzeix_palencia_of_convexThickening_hasMergelyanPolynomialApproximation
    A Omega hcarrier
  intro n
  exact (Omega n).hasMergelyanPolynomialApproximation
