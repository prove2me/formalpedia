-- Prove2me | solution 1 for re_inner_aeval_crouzeixProductRemainderPolynomial_nonneg_of_cauchy_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:20:12.369464+00:00
-- url     : https://prove2.me/submissions/4e0263f6-b3c5-44d7-b9e3-c777a5941143

import Definitions.Def_Operator_Crouzeix_ApproximationSupNorm
import Definitions.Def_Operator_Crouzeix_DoubleLayer
import Definitions.Def_Operator_Crouzeix_DoubleLayerIntegral
import Definitions.Def_Operator_Crouzeix_PositiveIntegral
import Definitions.Def_Operator_Crouzeix_ProductContour
import Definitions.Def_Operator_Crouzeix_SymmetrizedAuxiliary
import Definitions.Def_Operator_Crouzeix_SymmetrizedBound
import Definitions.Def_Operator_Crouzeix_GeneralSymmetrized
import Theorems.Thm_isPositive_aeval_crouzeixProductRemainderPolynomial_add_adjoint_of_cauchy_support

set_option autoImplicit false
open Complex MeasureTheory Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier)
    (hCauchyP : Polynomial.aeval A p =
      (2 * (Real.pi : ℂ) * I)⁻¹ •
        contourIntegral (fun z => Polynomial.eval z p • resolvent A z)
          Omega.boundaryParam)
    (hCauchyOne : (∫ t in (0 : ℝ)..(2 * Real.pi),
      deriv Omega.boundaryParam t • resolvent A (Omega.boundaryParam t)) =
        (2 * (Real.pi : ℂ) * I) • (1 : E →L[ℂ] E))
    (hsupport : ∀ t ∈ Ioc (0 : ℝ) (2 * Real.pi),
      ∀ w ∈ numericalRange A,
        ((starRingEnd ℂ) (-I * deriv Omega.boundaryParam t) *
          (w - Omega.boundaryParam t)).re ≤ 0)
    (x : E) :
    0 ≤ RCLike.re ⟪x,
      Polynomial.aeval A (crouzeixProductRemainderPolynomial Omega p) x⟫_ℂ := by
  let H := Polynomial.aeval A
    (crouzeixProductRemainderPolynomial Omega p)
  have hpos :=
    isPositive_aeval_crouzeixProductRemainderPolynomial_add_adjoint_of_cauchy_support
      A Omega p hOmega hCauchyP hCauchyOne hsupport
  have hreal := hpos.re_inner_nonneg_right x
  have hadjoint : RCLike.re ⟪x, star H x⟫_ℂ =
      RCLike.re ⟪x, H x⟫_ℂ := by
    change RCLike.re ⟪x, ContinuousLinearMap.adjoint H x⟫_ℂ = _
    rw [ContinuousLinearMap.adjoint_inner_right]
    exact inner_re_symm _ _
  change 0 ≤ RCLike.re ⟪x, H x⟫_ℂ
  change 0 ≤ RCLike.re ⟪x, (H + star H) x⟫_ℂ at hreal
  rw [add_apply, inner_add_right, map_add, hadjoint] at hreal
  linarith
