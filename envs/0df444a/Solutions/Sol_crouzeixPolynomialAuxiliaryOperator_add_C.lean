-- Prove2me | solution 1 for crouzeixPolynomialAuxiliaryOperator_add_C
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:38:48.058884+00:00
-- url     : https://prove2.me/submissions/a495b9bb-3aaa-4245-a33e-65da3d3135a9

import Definitions.Def_Operator_Crouzeix_ProductContour
import Definitions.Def_Operator_Crouzeix_VonNeumann
import Definitions.Def_Operator_Crouzeix_ProductBase
import Theorems.Thm_crouzeixPolynomialAuxiliaryOperator_C_eq_star_smul_one
import Theorems.Thm_crouzeixPolynomialAuxiliaryOperator_add


set_option autoImplicit false
open Complex Polynomial Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem _root_.solution
    [CompleteSpace E] (A : E →L[ℂ] E) (Omega : SmoothJordanDomain)
    (p : Polynomial ℂ) (a : ℂ)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier)
    (hCauchy : contourIntegral (resolvent A) Omega.boundaryParam =
      (2 * (Real.pi : ℂ) * Complex.I) • (1 : E →L[ℂ] E)) :
    crouzeixPolynomialAuxiliaryOperator A Omega (p + Polynomial.C a) =
      crouzeixPolynomialAuxiliaryOperator A Omega p +
        star a • (1 : E →L[ℂ] E) := by
  rw [crouzeixPolynomialAuxiliaryOperator_add A Omega p (Polynomial.C a) hOmega,
    crouzeixPolynomialAuxiliaryOperator_C_eq_star_smul_one A Omega a hCauchy]
