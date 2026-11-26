-- Prove2me | solution 1 for polytopeDirectionalValue_smoothSupportCurve_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:27:42.563919+00:00
-- url     : https://prove2.me/submissions/39e5b4e6-2443-4f42-8b45-c76725ec8967

import Definitions.Def_Operator_Crouzeix_SmoothSupportCurve
import Definitions.Def_Operator_Crouzeix_SmoothSupportEnvelopeApproximation
import Definitions.Def_Operator_Crouzeix_SmoothSupportCurveGlobal
import Theorems.Thm_strictMonoOn_smoothSupportCurve_projection_left
import Theorems.Thm_strictAntiOn_smoothSupportCurve_projection_right
import Theorems.Thm_exists_sub_int_mul_two_pi_mem_Ico
import Theorems.Thm_periodic_smoothSupportCurve
import Theorems.Thm_polytopeDirectionalValue_smoothSupportCurve_self


set_option autoImplicit false
open Complex Metric Set
open scoped ContDiff
theorem _root_.solution
    {h : ℝ → ℝ} (hsmooth : ContDiff ℝ ∞ h)
    (hperiodic : Function.Periodic h (2 * Real.pi))
    (hcurv : ∀ x, 0 < smoothSupportCurvatureRadius h x)
    (theta phi : ℝ) :
    polytopeDirectionalValue (smoothSupportCurve h phi) theta ≤ h theta := by
  obtain ⟨k, hk⟩ := exists_sub_int_mul_two_pi_mem_Ico theta phi
  let psi : ℝ := phi - (k : ℝ) * (2 * Real.pi)
  have hcurvePeriod := periodic_smoothSupportCurve hperiodic
  have hcurveEq : smoothSupportCurve h psi = smoothSupportCurve h phi := by
    exact hcurvePeriod.sub_int_mul_eq k
  rw [← hcurveEq]
  have hthetaSelf := polytopeDirectionalValue_smoothSupportCurve_self h theta
  by_cases hleft : psi ≤ theta
  · have hmono :=
      (strictMonoOn_smoothSupportCurve_projection_left
        hsmooth hcurv theta).monotoneOn
    have hle := hmono
      (show psi ∈ Icc (theta - Real.pi) theta from ⟨hk.1, hleft⟩)
      (show theta ∈ Icc (theta - Real.pi) theta from
        ⟨by linarith [Real.pi_pos], le_rfl⟩) hleft
    change polytopeDirectionalValue (smoothSupportCurve h psi) theta ≤
      polytopeDirectionalValue (smoothSupportCurve h theta) theta at hle
    rwa [hthetaSelf] at hle
  · have hthetaPsi : theta < psi := lt_of_not_ge hleft
    have hanti := strictAntiOn_smoothSupportCurve_projection_right
      hsmooth hcurv theta
    have hlt := hanti
      (show theta ∈ Icc theta (theta + Real.pi) from
        ⟨le_rfl, by linarith [Real.pi_pos]⟩)
      (show psi ∈ Icc theta (theta + Real.pi) from
        ⟨hthetaPsi.le, hk.2.le⟩) hthetaPsi
    change polytopeDirectionalValue (smoothSupportCurve h psi) theta <
      polytopeDirectionalValue (smoothSupportCurve h theta) theta at hlt
    rw [hthetaSelf] at hlt
    exact hlt.le
