-- Prove2me | solution 1 for exists_tight_regular_polytopeRoundedSupportCurve
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:26:20.515534+00:00
-- url     : https://prove2.me/submissions/94d75b95-cbbd-48ba-8603-f383610fe828

import Definitions.Def_Operator_Crouzeix_SmoothSupportEnvelopeApproximation
import Definitions.Def_Operator_Crouzeix_SmoothSupportCurve
import Definitions.Def_Operator_Crouzeix_SmoothSupportEnvelopeTight
import Theorems.Thm_exists_tight_polytopeRoundedSupportEnvelope
import Theorems.Thm_contDiff_polytopeRoundedSupportCurve
import Theorems.Thm_periodic_polytopeRoundedSupportCurve
import Theorems.Thm_polytopeRoundedSupportCurve_regular


set_option autoImplicit false
open Complex Metric Set
open scoped ContDiff
theorem _root_.solution
    {u : Finset ℂ} (hu : u.Nonempty) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ delta rho : ℝ,
      0 < delta ∧ 0 < rho ∧
      convexHull ℝ (u : Set ℂ) ⊆
        smoothSupportOpenEnvelope
          (polytopeRoundedSupport u delta rho) ∧
      closure
          (smoothSupportOpenEnvelope
            (polytopeRoundedSupport u delta rho)) ⊆
        Metric.thickening epsilon (convexHull ℝ (u : Set ℂ)) ∧
      Function.Periodic (polytopeRoundedSupportCurve u delta rho)
        (2 * Real.pi) ∧
      ContDiff ℝ ∞ (polytopeRoundedSupportCurve u delta rho) ∧
      ∀ theta, deriv (polytopeRoundedSupportCurve u delta rho) theta ≠ 0 := by
  obtain ⟨delta, rho, hdelta, hrho, hin, hout⟩ :=
    exists_tight_polytopeRoundedSupportEnvelope hu hepsilon
  exact ⟨delta, rho, hdelta, hrho, hin, hout,
    periodic_polytopeRoundedSupportCurve u delta rho,
    contDiff_polytopeRoundedSupportCurve hu delta rho,
    polytopeRoundedSupportCurve_regular hu hdelta hrho⟩
