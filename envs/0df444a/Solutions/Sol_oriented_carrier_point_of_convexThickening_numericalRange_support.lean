-- Prove2me | solution 1 for oriented_carrier_point_of_convexThickening_numericalRange_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:49:14.92441+00:00
-- url     : https://prove2.me/submissions/8dfd96f3-4621-4ef1-93b7-08cd0d26f5aa

import Definitions.Def_Operator_Crouzeix_PolynomialCauchyFromResolventMass
import Definitions.Def_Operator_Crouzeix_ResolventContourHomotopy
import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasureMass
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadialAssembly
import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasureAssembly
import Theorems.Thm_canonicalNormal_support_all_of_Ioc


set_option autoImplicit false
open Complex MeasureTheory Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
omit [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) (Omega : ℕ → SmoothJordanDomain)
    (hcarrier : ∀ n, (Omega n).carrier =
      convexThickeningApprox (closure (numericalRange A)) n)
    (hsupport : ∀ (n : ℕ) (t : ℝ),
      t ∈ Ioc (0 : ℝ) (2 * Real.pi) →
      ∀ w ∈ numericalRange A,
        ((starRingEnd ℂ) (-I * deriv (Omega n).boundaryParam t) *
          (w - (Omega n).boundaryParam t)).re ≤ 0) :
    ∀ n, ∃ w ∈ (Omega n).carrier, ∀ t : ℝ,
      ((starRingEnd ℂ) (-I * deriv (Omega n).boundaryParam t) *
        (w - (Omega n).boundaryParam t)).re ≤ 0 := by
  intro n
  have hr : 0 < smoothApproxRadius n := by
    unfold smoothApproxRadius
    positivity
  have hstage : (Omega n).carrier.Nonempty :=
    (Omega n).carrier_nonempty
  rw [hcarrier n] at hstage
  have hK : (closure (numericalRange A)).Nonempty := by
    change (Metric.thickening (smoothApproxRadius n)
      (closure (numericalRange A))).Nonempty at hstage
    exact (Metric.thickening_nonempty_iff_of_pos hr).mp hstage
  obtain ⟨w, hw⟩ := hK.of_closure
  have hwOmega : w ∈ (Omega n).carrier := by
    rw [hcarrier n]
    exact Metric.self_subset_thickening hr _ (subset_closure hw)
  refine ⟨w, hwOmega, ?_⟩
  apply canonicalNormal_support_all_of_Ioc
  intro t ht
  exact hsupport n t ht w hw
