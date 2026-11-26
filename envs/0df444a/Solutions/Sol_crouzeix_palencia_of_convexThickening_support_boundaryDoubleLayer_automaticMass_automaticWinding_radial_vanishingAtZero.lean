-- Prove2me | solution 1 for crouzeix_palencia_of_convexThickening_support_boundaryDoubleLayer_automaticMass_automaticWinding_radial_vanishingAtZero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:35:06.345893+00:00
-- url     : https://prove2.me/submissions/5bf1be7d-e3b0-4206-ad08-ae6670012d37

import Definitions.Def_Operator_Crouzeix_PolynomialCauchyFromResolventMass
import Definitions.Def_Operator_Crouzeix_ResolventContourHomotopy
import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasureMass
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadialAssembly
import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasureAssembly
import Theorems.Thm_oriented_carrier_point_of_convexThickening_numericalRange_support
import Theorems.Thm_crouzeix_palencia_of_convexThickening_resolventMass_support_boundaryDoubleLayer_automaticWinding_radial_vanishingAtZero
import Theorems.Thm_contourIntegral_resolvent_eq_two_pi_I_smul_one_of_oriented_convex_carrier
import Theorems.Thm_convexThickeningApprox_spec
import Theorems.Thm_convex_numericalRange
import Theorems.Thm_norm_le_of_mem_numericalRange


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
    (hsupport : ∀ (n : ℕ) (t : ℝ),
      t ∈ Ioc (0 : ℝ) (2 * Real.pi) →
      ∀ w ∈ numericalRange A,
        ((starRingEnd ℂ) (-I * deriv (Omega n).boundaryParam t) *
          (w - (Omega n).boundaryParam t)).re ≤ 0)
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
    crouzeix_palencia_of_convexThickening_resolventMass_support_boundaryDoubleLayer_automaticWinding_radial_vanishingAtZero
      A Omega hcarrier
  · intro n
    obtain ⟨c, hc, hcside⟩ :=
      oriented_carrier_point_of_convexThickening_numericalRange_support
        A Omega hcarrier hsupport n
    apply
      contourIntegral_resolvent_eq_two_pi_I_smul_one_of_oriented_convex_carrier
        A (Omega n) c hc hcside
    rw [hcarrier n]
    have hcompact : IsCompact (closure (numericalRange A)) := by
      have hbounded : Bornology.IsBounded (numericalRange A) :=
        Metric.isBounded_closedBall.subset (fun z hz => by
          rw [Metric.mem_closedBall, dist_zero_right]
          exact norm_le_of_mem_numericalRange A hz)
      exact hbounded.isCompact_closure
    exact
      (convexThickeningApprox_spec (closure (numericalRange A)) hcompact
        (convex_numericalRange A).closure).1 n |>.1
  · exact hsupport
  · exact happrox
  · exact hPlemelj
