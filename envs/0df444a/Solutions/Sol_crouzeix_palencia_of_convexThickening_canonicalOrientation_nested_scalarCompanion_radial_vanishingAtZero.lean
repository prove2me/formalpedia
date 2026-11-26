-- Prove2me | solution 1 for crouzeix_palencia_of_convexThickening_canonicalOrientation_nested_scalarCompanion_radial_vanishingAtZero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:25:09.162728+00:00
-- url     : https://prove2.me/submissions/90be8d90-78b8-4927-a8ad-8271ca0ded0e

import Definitions.Def_Operator_Crouzeix_ResolventContourHomotopy
import Definitions.Def_Operator_Crouzeix_PalenciaSmoothApproximation
import Definitions.Def_Operator_Crouzeix_PolynomialCauchyFromResolventMass
import Definitions.Def_Operator_Crouzeix_ResolventCauchyKernel
import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasureMass
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadialAssembly
import Definitions.Def_Operator_Crouzeix_SmoothJordanExhaustion
import Theorems.Thm_crouzeix_palencia_of_convexThickening_pointOriented_nested_scalarCompanion_radial_vanishingAtZero
import Theorems.Thm_SmoothJordanDomain_canonicalOrientation_carrier
import Theorems.Thm_SmoothJordanDomain_exists_oriented_point_canonicalOrientation
attribute [local simp] SmoothJordanDomain.canonicalOrientation_carrier



set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) (Omega : ℕ → SmoothJordanDomain)
    (hcarrier : ∀ n, (Omega n).carrier =
      convexThickeningApprox (closure (numericalRange A)) n)
    (happrox : ∀ (p : Polynomial ℂ) (n : ℕ), 0 < p.natDegree →
      Polynomial.eval 0 p = 0 →
      ∃ r : ℕ → Polynomial ℂ,
        ∀ (j : ℕ) (z : ℂ),
          z ∈ compactThickeningApprox (closure (numericalRange A)) n →
          ‖Polynomial.eval z (r j) -
            crouzeixPolynomialScalarCompanionClosedExtension
              (Omega n).canonicalOrientation p z‖ ≤
            1 / ((j : ℝ) + 1)) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by
  apply
    crouzeix_palencia_of_convexThickening_pointOriented_nested_scalarCompanion_radial_vanishingAtZero
      A (fun n ↦ (Omega n).canonicalOrientation)
  · intro n
    rw [SmoothJordanDomain.canonicalOrientation_carrier, hcarrier n]
  · exact fun n ↦ (Omega n).exists_oriented_point_canonicalOrientation
  · exact happrox
