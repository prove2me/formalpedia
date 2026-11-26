-- Prove2me | solution 1 for crouzeix_palencia_of_convexThickening_cauchy_support_boundaryDoubleLayerProbability_radial_vanishingAtZero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:06:32.947428+00:00
-- url     : https://prove2.me/submissions/35c8e241-8791-4bc5-83b4-1f44ee0c55a4

import Definitions.Def_Operator_Crouzeix_PolynomialCauchyFromResolventMass
import Definitions.Def_Operator_Crouzeix_ResolventContourHomotopy
import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasureMass
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadialAssembly
import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasureAssembly
import Theorems.Thm_crouzeix_palencia_of_convexThickening_cauchy_support_boundaryDoubleLayerDensity_radial_vanishingAtZero
import Theorems.Thm_intervalIntegrable_crouzeixBoundaryDoubleLayerDensity_of_integral_eq_one


set_option autoImplicit false
open Complex MeasureTheory Set
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
    (hmass : ∀ (n : ℕ) (xi : ℂ),
      xi ∈ frontier (Omega n).carrier →
      (∫ t in (0 : ℝ)..(2 * Real.pi),
        crouzeixBoundaryDoubleLayerDensity (Omega n) xi t) = 1)
    (hboundarySupport : ∀ (n : ℕ) (xi : ℂ),
      xi ∈ frontier (Omega n).carrier →
      ∀ t ∈ Ioc (0 : ℝ) (2 * Real.pi),
        ((starRingEnd ℂ) (-I * deriv (Omega n).boundaryParam t) *
          (xi - (Omega n).boundaryParam t)).re ≤ 0)
    (happrox : ∀ (p : Polynomial ℂ) (n : ℕ), 0 < p.natDegree →
      Polynomial.eval 0 p = 0 →
      ∃ r : ℕ → Polynomial ℂ,
        ∀ (j : ℕ) (z : ℂ),
          z ∈ compactThickeningApprox (closure (numericalRange A)) n →
          ‖Polynomial.eval z (r j) -
              crouzeixPolynomialScalarCompanionClosedExtension
                (Omega n) p z‖ ≤
            1 / ((j : ℝ) + 1))
    (hPlemelj : ∀ (p : Polynomial ℂ) (n : ℕ), 0 < p.natDegree →
      Polynomial.eval 0 p = 0 →
      polynomialSupNorm p (frontier (Omega n).carrier) = 1 →
      crouzeixAuxiliaryOperator A (Omega n)
          (crouzeixPolynomialScalarCompanionClosedExtension (Omega n) p) =
        crouzeixPolynomialAuxiliaryOperator A (Omega n) p) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by
  apply
    crouzeix_palencia_of_convexThickening_cauchy_support_boundaryDoubleLayerDensity_radial_vanishingAtZero
      A Omega hcarrier hCauchyP hsupport hkernel
  · intro n xi hxi
    exact
      intervalIntegrable_crouzeixBoundaryDoubleLayerDensity_of_integral_eq_one
        (Omega n) xi (hmass n xi hxi)
  · exact hmass
  · exact hboundarySupport
  · exact happrox
  · exact hPlemelj
