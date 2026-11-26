-- Prove2me | solution 1 for crouzeix_palencia_of_convexThickening_cauchy_support_boundaryPhase_radial_approximation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:18:45.658802+00:00
-- url     : https://prove2.me/submissions/278b7e26-afbf-4305-be4f-b7b64cbdec78

import Definitions.Def_Operator_Crouzeix_ScalarCompanionAssembly
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPhaseInduction
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadialAssembly
import Theorems.Thm_crouzeix_palencia_of_convexThickening_cauchy_support_boundaryPhase_approximation
import Theorems.Thm_tendsto_crouzeixPolynomialScalarCompanionRegularized_of_cauchyKernel_eq_one


set_option autoImplicit false
open Complex Filter Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) (Omega : ℕ → SmoothJordanDomain)
    (hcarrier : ∀ n, (Omega n).carrier =
      convexThickeningApprox (closure (numericalRange A)) n)
    (hCauchyP : ∀ (p : Polynomial ℂ) (n : ℕ),
      Polynomial.aeval A p =
        (2 * (Real.pi : ℂ) * I)⁻¹ •
          contourIntegral
            (fun z => Polynomial.eval z p • resolvent A z)
            (Omega n).boundaryParam)
    (hsupport : ∀ (n : ℕ) (t : ℝ),
      t ∈ Ioc (0 : ℝ) (2 * Real.pi) →
      ∀ w ∈ numericalRange A,
        ((starRingEnd ℂ) (-I * deriv (Omega n).boundaryParam t) *
          (w - (Omega n).boundaryParam t)).re ≤ 0)
    (hkernel : ∀ (n : ℕ) (z : ℂ), z ∈ (Omega n).carrier →
      crouzeixScalarCauchyKernel (Omega n) z = 1)
    (hphase : ∀ (p : Polynomial ℂ) (n : ℕ)
      (xi : ℂ), xi ∈ frontier (Omega n).carrier →
      ‖star (Polynomial.eval xi p) +
          crouzeixPolynomialBoundaryPhaseTransform (Omega n) xi
            (p /ₘ (Polynomial.X - Polynomial.C xi))‖ ≤
        polynomialSupNorm p (frontier (Omega n).carrier))
    (happrox : ∀ (p : Polynomial ℂ) (n : ℕ),
      ∃ r : ℕ → Polynomial ℂ,
        ∀ (j : ℕ) (z : ℂ),
          z ∈ compactThickeningApprox (closure (numericalRange A)) n →
          ‖Polynomial.eval z (r j) -
              crouzeixPolynomialScalarCompanionClosedExtension
                (Omega n) p z‖ ≤
            1 / ((j : ℝ) + 1))
    (hPlemelj : ∀ (p : Polynomial ℂ) (n : ℕ),
      crouzeixAuxiliaryOperator A (Omega n)
          (crouzeixPolynomialScalarCompanionClosedExtension (Omega n) p) =
        crouzeixPolynomialAuxiliaryOperator A (Omega n) p) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by
  apply
    crouzeix_palencia_of_convexThickening_cauchy_support_boundaryPhase_approximation
      A Omega hcarrier hCauchyP hsupport hkernel
  · intro p n xi hxi
    exact
      tendsto_crouzeixPolynomialScalarCompanionRegularized_of_cauchyKernel_eq_one
        (Omega n) p (hkernel n) hxi
  · exact hphase
  · exact happrox
  · exact hPlemelj
