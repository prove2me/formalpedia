-- Prove2me | solution 1 for crouzeix_palencia_of_convexThickening_pointOriented_nested_scalarCompanion_radial_vanishingAtZero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:28:36.459252+00:00
-- url     : https://prove2.me/submissions/1cc3659b-3ba9-4c4c-a985-1eb7aba68a42

import Definitions.Def_Operator_Crouzeix_ResolventContourHomotopy
import Definitions.Def_Operator_Crouzeix_PalenciaSmoothApproximation
import Definitions.Def_Operator_Crouzeix_PolynomialCauchyFromResolventMass
import Definitions.Def_Operator_Crouzeix_ResolventCauchyKernel
import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasureMass
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadialAssembly
import Definitions.Def_Operator_Crouzeix_SmoothJordanExhaustion
import Theorems.Thm_crouzeix_palencia_of_convexThickening_support_nested_scalarCompanion_radial_vanishingAtZero
import Theorems.Thm_SmoothJordanDomain_canonicalNormal_support_all_of_support_at
import Theorems.Thm_SmoothJordanDomain_closure_support_and_carrier_strict_of_support_at_mem_carrier


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
    (horientation : ∀ n, ∃ c ∈ (Omega n).carrier,
      ((starRingEnd ℂ) (-I * deriv (Omega n).boundaryParam 0) *
        (c - (Omega n).boundaryParam 0)).re ≤ 0)
    (happrox : ∀ (p : Polynomial ℂ) (n : ℕ), 0 < p.natDegree →
      Polynomial.eval 0 p = 0 →
      ∃ r : ℕ → Polynomial ℂ,
        ∀ (j : ℕ) (z : ℂ),
          z ∈ compactThickeningApprox (closure (numericalRange A)) n →
          ‖Polynomial.eval z (r j) -
            crouzeixPolynomialScalarCompanionClosedExtension
              (Omega n) p z‖ ≤ 1 / ((j : ℝ) + 1)) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by
  apply
    crouzeix_palencia_of_convexThickening_support_nested_scalarCompanion_radial_vanishingAtZero
      A Omega hcarrier
  · intro n t _ht w hw
    obtain ⟨c, hc, hc0⟩ := horientation n
    have hcside :=
      (Omega n).canonicalNormal_support_all_of_support_at c hc 0 hc0 t
    have hwcarrier : w ∈ (Omega n).carrier := by
      rw [hcarrier n]
      apply Metric.self_subset_thickening
      · unfold smoothApproxRadius
        positivity
      · exact subset_closure hw
    exact
      ((Omega n).closure_support_and_carrier_strict_of_support_at_mem_carrier
        c hc t hcside).2 w hwcarrier |>.le
  · exact happrox
