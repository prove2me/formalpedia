-- Prove2me | solution 1 for polytopeDirectionalValue_le_roundedSupportCurve_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:25:50.140253+00:00
-- url     : https://prove2.me/submissions/451e2710-cd68-4caa-8852-4a85e512b30c

import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupportCurvature
import Definitions.Def_Operator_Crouzeix_SmoothSupportCurve
import Theorems.Thm_polytopeDirectionalValue_smoothSupportCurve_self
import Theorems.Thm_polytopeDirectionalValue_le_softSupport_of_mem_convexHull


set_option autoImplicit false
open Complex Set
open scoped ContDiff
theorem _root_.solution
    {u : Finset ℂ} {z : ℂ} (hz : z ∈ convexHull ℝ (u : Set ℂ))
    {delta rho : ℝ} (hdelta : 0 < delta) (hrho : 0 ≤ rho)
    (theta : ℝ) :
    polytopeDirectionalValue z theta ≤
      polytopeDirectionalValue
        (polytopeRoundedSupportCurve u delta rho theta) theta := by
  unfold polytopeRoundedSupportCurve
  rw [polytopeDirectionalValue_smoothSupportCurve_self]
  unfold polytopeRoundedSupport
  exact (polytopeDirectionalValue_le_softSupport_of_mem_convexHull
    hz hdelta theta).trans (le_add_of_nonneg_right hrho)
