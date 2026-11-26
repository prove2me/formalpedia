-- Prove2me | solution 1 for polytopeSoftSupport_add_deriv_deriv_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:25:14.360893+00:00
-- url     : https://prove2.me/submissions/76184188-a9c0-4be8-a29c-dcb88665f02f

import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupport
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupportCurvature
import Theorems.Thm_deriv_deriv_polytopeSoftSupport
import Theorems.Thm_polytopeSoftSupport_add_second_nonneg

set_option autoImplicit false
open Complex Set
open scoped ContDiff
theorem _root_.solution
    {u : Finset ℂ} (hu : u.Nonempty) {delta : ℝ} (hdelta : 0 < delta)
    (theta : ℝ) :
    0 ≤ polytopeSoftSupport u delta theta +
      deriv (deriv (polytopeSoftSupport u delta)) theta := by
  rw [deriv_deriv_polytopeSoftSupport hu delta theta]
  exact polytopeSoftSupport_add_second_nonneg hu hdelta theta
