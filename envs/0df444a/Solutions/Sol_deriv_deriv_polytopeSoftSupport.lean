-- Prove2me | solution 1 for deriv_deriv_polytopeSoftSupport
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:24:16.476146+00:00
-- url     : https://prove2.me/submissions/eacc3f0d-89cb-438c-b0b6-166217b9c852

import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupport
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupportCurvature
import Theorems.Thm_hasDerivAt_polytopeSoftSupportFirst
import Theorems.Thm_deriv_polytopeSoftSupport

set_option autoImplicit false
open Complex Set
open scoped ContDiff
theorem _root_.solution
    {u : Finset ℂ} (hu : u.Nonempty) (delta theta : ℝ) :
    deriv (deriv (polytopeSoftSupport u delta)) theta =
      polytopeSoftSupportSecond u delta theta := by
  have hfirst : deriv (polytopeSoftSupport u delta) =
      polytopeSoftSupportFirst u delta := by
    funext x
    exact deriv_polytopeSoftSupport hu delta x
  rw [hfirst]
  exact (hasDerivAt_polytopeSoftSupportFirst hu delta theta).deriv
