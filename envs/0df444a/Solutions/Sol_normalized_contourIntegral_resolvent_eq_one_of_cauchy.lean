-- Prove2me | solution 1 for normalized_contourIntegral_resolvent_eq_one_of_cauchy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:37:14.247438+00:00
-- url     : https://prove2.me/submissions/9a11d9bc-96b7-4e47-b37f-3bfac044eb29

import Definitions.Def_Operator_Crouzeix_ProductContour
import Definitions.Def_Operator_Crouzeix_VonNeumann
import Definitions.Def_Operator_Crouzeix_ProductBase

set_option autoImplicit false
open Complex Polynomial Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem _root_.solution [CompleteSpace E]
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain)
    (hCauchy : contourIntegral (resolvent A) Omega.boundaryParam =
      (2 * (Real.pi : ℂ) * Complex.I) • (1 : E →L[ℂ] E)) :
    (2 * (Real.pi : ℂ) * Complex.I)⁻¹ •
        contourIntegral (resolvent A) Omega.boundaryParam = 1 := by
  rw [hCauchy, smul_smul]
  rw [inv_mul_cancel₀]
  · exact one_smul _ _
  · exact mul_ne_zero
      (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
