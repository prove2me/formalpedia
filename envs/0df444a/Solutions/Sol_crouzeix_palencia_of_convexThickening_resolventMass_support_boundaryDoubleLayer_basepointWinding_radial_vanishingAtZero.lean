-- Prove2me | solution 1 for crouzeix_palencia_of_convexThickening_resolventMass_support_boundaryDoubleLayer_basepointWinding_radial_vanishingAtZero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:12:00.457403+00:00
-- url     : https://prove2.me/submissions/0d10d004-0234-41a0-a635-0b6536ceacab

import Definitions.Def_Operator_Crouzeix_PolynomialCauchyFromResolventMass
import Definitions.Def_Operator_Crouzeix_ResolventContourHomotopy
import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasureMass
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadialAssembly
import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasureAssembly
import Theorems.Thm_crouzeix_palencia_of_convexThickening_resolventMass_support_boundaryDoubleLayer_radial_vanishingAtZero
import Theorems.Thm_crouzeixScalarCauchyKernel_eq_one_of_basepoint


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
    (hmass : ∀ n,
      contourIntegral (resolvent A) (Omega n).boundaryParam =
        (2 * (Real.pi : ℂ) * I) • (1 : E →L[ℂ] E))
    (hsupport : ∀ (n : ℕ) (t : ℝ),
      t ∈ Ioc (0 : ℝ) (2 * Real.pi) →
      ∀ w ∈ numericalRange A,
        ((starRingEnd ℂ) (-I * deriv (Omega n).boundaryParam t) *
          (w - (Omega n).boundaryParam t)).re ≤ 0)
    (hwind : ∀ n, ∃ c ∈ (Omega n).carrier,
      crouzeixScalarCauchyKernel (Omega n) c = 1)
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
    crouzeix_palencia_of_convexThickening_resolventMass_support_boundaryDoubleLayer_radial_vanishingAtZero
      A Omega hcarrier hmass hsupport
  · intro n z hz
    obtain ⟨c, hc, hkc⟩ := hwind n
    exact crouzeixScalarCauchyKernel_eq_one_of_basepoint
      (Omega n) c hc hkc z hz
  · exact happrox
  · exact hPlemelj
