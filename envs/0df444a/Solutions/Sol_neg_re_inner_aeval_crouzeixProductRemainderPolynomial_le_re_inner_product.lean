-- Prove2me | solution 1 for neg_re_inner_aeval_crouzeixProductRemainderPolynomial_le_re_inner_product
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:20:00.750082+00:00
-- url     : https://prove2.me/submissions/46d22653-26b9-4cbd-9399-d314074092c2

import Definitions.Def_Operator_Crouzeix_ApproximationSupNorm
import Definitions.Def_Operator_Crouzeix_DoubleLayer
import Definitions.Def_Operator_Crouzeix_DoubleLayerIntegral
import Definitions.Def_Operator_Crouzeix_PositiveIntegral
import Definitions.Def_Operator_Crouzeix_ProductContour
import Definitions.Def_Operator_Crouzeix_SymmetrizedAuxiliary
import Definitions.Def_Operator_Crouzeix_SymmetrizedBound
import Definitions.Def_Operator_Crouzeix_GeneralSymmetrized
import Theorems.Thm_re_inner_crouzeixSquareAuxiliaryOperator_nonneg_of_support
import Theorems.Thm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_eq_squareAux_sub_aeval_remainderPolynomial


set_option autoImplicit false
open Complex MeasureTheory Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier)
    (hsupport : ∀ t ∈ Ioc (0 : ℝ) (2 * Real.pi),
      ∀ w ∈ numericalRange A,
        ((starRingEnd ℂ) (-I * deriv Omega.boundaryParam t) *
          (w - Omega.boundaryParam t)).re ≤ 0)
    (x : E) :
    -RCLike.re ⟪x,
        Polynomial.aeval A (crouzeixProductRemainderPolynomial Omega p) x⟫_ℂ ≤
      RCLike.re ⟪x, (Polynomial.aeval A p *
        crouzeixPolynomialAuxiliaryOperator A Omega p) x⟫_ℂ := by
  have hsquare := re_inner_crouzeixSquareAuxiliaryOperator_nonneg_of_support
    A Omega p hOmega hsupport x
  have hidentity :=
    aeval_mul_crouzeixPolynomialAuxiliaryOperator_eq_squareAux_sub_aeval_remainderPolynomial
      A Omega p hOmega
  rw [hidentity, sub_apply, inner_sub_right, map_sub]
  linarith
